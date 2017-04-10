#!/usr/bin/env python

import re
import sys
import copy
import collections
import logging
import time

DIM_SIP, DIM_DIP, DIM_SPORT, DIM_DPORT, DIM_PROTO, DIM_MAX = range(6)
UINT32_MAX, UINT16_MAX, UINT8_MAX = ((1 << i) - 1 for i in [32, 16, 8])
DIM_POINT_MAX = [UINT32_MAX, UINT32_MAX, UINT16_MAX, UINT16_MAX, UINT8_MAX]

BIT_RANGE = [(0,31),(32,63),(64,79),(80,95),(96,103)]
FIELD_LENTH = [32, 32, 16, 16, 8]
BIT_LENTH = 104
BINTH = 8
SPFAC = 4


stat = {}

NON_LEAF_BUCKET_STRUCTURE_SIZE = 13 + 4 + 4
LEAF_BUCKET_STRUCTURE_SIZE = 4
LINEAR_BUCKET_SIZE = 4


# rule format:
# [[sip_begin, sip_end, sip_mask_len], [dip_begin, dip_end, dip_mask_len] ..., [proto_begin, proto_end], [pri]]
def load_rules(s_rule_file):
    rule_set = []
    rule_set_text = []
    rule_fmt = re.compile(r'^@(\d+).(\d+).(\d+).(\d+)/(\d+) ' \
            r'(\d+).(\d+).(\d+).(\d+)/(\d+) ' \
            r'(\d+) : (\d+) ' \
            r'(\d+) : (\d+) ' \
            r'(0x[\da-fA-F]+)/(0x[\da-fA-F]+)$')

    for idx, line in enumerate(open(s_rule_file)):
        sip0, sip1, sip2, sip3, sip_mask_len, \
        dip0, dip1, dip2, dip3, dip_mask_len, \
        sport_begin, sport_end, \
        dport_begin, dport_end, \
        proto, proto_mask = \
        (eval(rule_fmt.match(line).group(i)) for i in range(1, 17))

        sip0 = (sip0 << 24) | (sip1 << 16) | (sip2 << 8) | sip3
        sip_begin = sip0 & (~((1 << (32 - sip_mask_len)) - 1))
        sip_end = sip0 | ((1 << (32 - sip_mask_len)) - 1)

        dip0 = (dip0 << 24) | (dip1 << 16) | (dip2 << 8) | dip3
        dip_begin = dip0 & (~((1 << (32 - dip_mask_len)) - 1))
        dip_end = dip0 | ((1 << (32 - dip_mask_len)) - 1)

        if proto_mask == 0xff:
            proto_begin = proto
            proto_end = proto
        else:
            proto_begin = 0
            proto_end = 0xff

        rule_set.append([[sip_begin, sip_end, sip_mask_len], [dip_begin, dip_end, dip_mask_len], \
                [sport_begin, sport_end], [dport_begin, dport_end], \
                [proto_begin, proto_end], [idx]])
        rule_set_text.append(line)

    return rule_set,rule_set_text


# Split the rule set into buckets according to the bit_array,
# each bucket contains a subset of rules
def split_rule_set(rule_set, bit_array):
    buckets = [[] for i in range(1<<len(bit_array))]
    for r in rule_set:
        split_rule(r, bit_array, buckets)
    max_bucket_size = 0
    max_bucket_num = 0
    bucket_size_stat = {}
    for b in buckets:
        if len(b) not in bucket_size_stat:
            bucket_size_stat[len(b)] = 0
        bucket_size_stat[len(b)] += 1
    max_bucket_size = max(bucket_size_stat.keys())
    max_bucket_num = bucket_size_stat[max_bucket_size]
    bucket_percentage_stat = {size:(float(num)/float(len(buckets))) for size, num in bucket_size_stat.iteritems()}
    return buckets, max_bucket_size, max_bucket_num, bucket_percentage_stat


# Called by split_rule_set, decides which bucket a rule belongs to given the bit array
def split_rule(rule, bit_array, buckets):
    len_bit_array = len(bit_array)
    for index in range(1<<len(bit_array)):
        index_in = 1
        for i, bit in enumerate(bit_array):
            index_mask=1<<(len_bit_array-1-i)
            if 0<=bit and bit<32:
                hash_bit = bit
                rule_mask = 1<<(31-hash_bit)
                if hash_bit+1 <= rule[0][2]:
                    if ((index&index_mask)>>(len_bit_array-1-i))!=((rule[0][0]&rule_mask)>>(31-hash_bit)):
                        index_in = 0
                        break
            elif 32<=bit and bit<64:
                hash_bit = bit - 32
                rule_mask = 1<<(31-hash_bit)
                if hash_bit+1 <= rule[1][2]:
                    if ((index&index_mask)>>(len_bit_array-1-i))!=((rule[1][0]&rule_mask)>>(31-hash_bit)):
                        index_in = 0
                        break
            elif 64<=bit and bit<80:
                hash_bit = bit - 64
                rule_mask = 1<<(15-hash_bit)
                if rule_mask > rule[2][1]-rule[2][0]:
                    port_xor = rule[2][1]^rule[2][0]
                    if (port_xor&rule_mask) == 0:
                        if (index&index_mask)>>(len_bit_array-1-i)!=(rule[2][0]&rule_mask)>>(15-hash_bit):
                            index_in = 0
                            break
            elif 80<=bit and bit<96:
                hash_bit = bit - 80
                rule_mask = 1<<(15-hash_bit)
                if rule_mask > rule[3][1]-rule[3][0]:
                    port_xor = rule[3][1]^rule[3][0]
                    if (port_xor&rule_mask) == 0:
                        if (index&index_mask)>>(len_bit_array-1-i)!=(rule[3][0]&rule_mask)>>(15-hash_bit):
                            index_in = 0
                            break
            elif 96<=bit and bit<104:
                hash_bit = bit - 96
                rule_mask = 1<<(7-hash_bit)
                if rule[4][1]-rule[4][0] != 255:
                    if (index&index_mask)>>(len_bit_array-1-i)!=(rule[4][0]&rule_mask)>>(7-hash_bit):
                        index_in = 0
                        break
        if index_in == 1:
            buckets[index].append(rule)


# Split the rules by selecting appropriate bits, a recursive function
# To write the split results to the result_file and calculate some metrics(memory access time, memory size, etc)
def bit_select_pairwise(rule_set, rule_set_text, level=0, super_array=[], message=''):
    global max_level
    global total_leaf_number
    global total_leaf_depth
    global max_leaf_depth
    global total_mem_size
    # global result_file
    global csvfile
    global csvfile2
    bit_info = {}   # format: {bit: pair_dict}, bit is the bit in 5-tuple rule, 
                    # pair_dict is the dictionary of rule pairs. All the pairs this bit could separate is set to 1  
    bit_size_info = {}
    pair_num = 0
    spliting_stucked = False

    if level > max_level:
        max_level = level
    avaliable_array = list(set(range(BIT_LENTH))-set(super_array))
    for i in avaliable_array:
        bit_info[i] = bit_separation_info(rule_set,i)
        bit_size_info[i] = pair_count(bit_info[i])
        if level == 0:
            logger.debug("bit %d : %d"%(i,bit_size_info[i]))
        pair_num += bit_size_info[i]
    max_bucket_size = len(rule_set)
    origin_rule_num = len(rule_set)
    max_bucket_num = 1
    if pair_num == 0:
        logger.debug("Can't continue to split by single bit")
        spliting_stucked = True
        return

    # Select bit for the classifier
    bit_array = []
    while max_bucket_size > 1:
        # Select the best bit in terms of "separability"
        sorted_bit_size_info = sorted(bit_size_info.items(), key=lambda x:x[1] ,reverse=True)
        # to prevent to be stucked
        if sorted_bit_size_info[0][1] == 0:
            logger.debug("Can't continue to split by single bit")
            spliting_stucked = True
            break
        bit_selected = sorted_bit_size_info[0][0]
        logger.debug("Add bit %d"%bit_selected)
        bit_array.append(bit_selected)
        # Since new bit will separate some rules, update the "pair_dict" info of each bit
        for bit, pair_dict in bit_info.iteritems():
            if bit != bit_selected:
                pair_dict_sub(bit_info[bit], bit_info[bit_selected])
                bit_size_info[bit] = pair_count(bit_info[bit])
        del bit_info[bit_selected]
        del bit_size_info[bit_selected]
        buckets, max_bucket_size, max_bucket_num, bucket_percentage_stat = split_rule_set(rule_set, bit_array)
        logger.debug("max_bucket_size %d, max_bucket_num %d"%(max_bucket_size, max_bucket_num))
        
        # Expansion is the space expansion coefficient of current node
        # It uses the origin space of current node to divide the space current split result takes
        # (sum(length(child_bucket)) + sum(child_bucket)) / (length(origin_bucket))
        new_rule_num = 0
        for (k,v) in bucket_percentage_stat.items():
            new_rule_num = new_rule_num + k * v * 2**(len(bit_array))
        Expansion = (new_rule_num + 2**(len(bit_array))) / float(origin_rule_num)
        # result_file.write("bit: %d, child_num: %d Expansion: %f\n"%(len(bit_array), new_rule_num, Expansion))
        
        # Stopping criteria
        if Expansion > SPFAC:
            break


    avg_children_rules = new_rule_num / float(2**(len(bit_array)))
    # Now that bit_info won't be used further, delete to save memory
    del bit_info

    if level == 0:
        # result_file.write("Basic bit array: %r\n\n"%bit_array)
        new_message = message
    else:
        new_message = message + str(bit_array) + '-' 
    bit_array = bit_array + super_array
    logger.debug("Current length %d bit_array: %r"%(len(bit_array),bit_array))
    # If rules of every bucket is no more than BINTH, it means every bucket is leaf node.
    # Then this level will be regarded as a bottom level
    if max_bucket_size <= BINTH:
        bottom_level = True
    else:
        bottom_level = False
    csvfile.write("%f\n"%(avg_children_rules/len(rule_set)))
    csvfile2.write("%f\n"%(float(max_bucket_size)/len(rule_set)))


    # Next level
    for i, subset in enumerate(buckets):
        # If rules of the bucket is more than BINTH and can be further splitted, this bucket is a non-leaf node
        # process the recursion
        if len(subset) > BINTH and spliting_stucked == False:
            total_mem_size += NON_LEAF_BUCKET_STRUCTURE_SIZE
            logger.debug("Level %d split of bucket %d"%(level+1,i))
            # result_file.write('\t' * level + new_message + str(i) + ': \n')
            bit_select_pairwise(subset,rule_set_text,level+1,bit_array,new_message)
        # Leaf-node
        # Write the rules split results to the result_file and calculate the metrics
        else:
            # if subset:
            #     for j, r in enumerate(subset):
            #         if j == 0:
            #             result_file.write('\t' * level + new_message + str(i) + ': ' + rule_set_text[r[DIM_MAX][0]][:-1] + '\n')
            #         else:
            #             result_file.write('\t' * level + len(new_message + str(i) + ': ') * ' ' + rule_set_text[r[DIM_MAX][0]][:-1] + '\n')
            total_leaf_number += 1
            total_leaf_depth += level + len(subset)
            if max_leaf_depth < level + len(subset):
                max_leaf_depth = level + len(subset)
            if bottom_level == True:
                total_mem_size += LEAF_BUCKET_STRUCTURE_SIZE + len(subset) * LINEAR_BUCKET_SIZE
            else:
                total_mem_size += NON_LEAF_BUCKET_STRUCTURE_SIZE + len(subset) * LINEAR_BUCKET_SIZE


    logger.debug("Level %d split finished"%(level))


# Generate bit separation information of the bit 
# mark all the pairs the bit can sperate in a pair dictionary and put the dictionary into bit_info
def bit_separation_info(rule_set, bit):
    # locate the dim and get the rule_mask
    if 0<=bit and bit<32:
        hash_bit = bit
        dim = 0
    elif 32<=bit and bit<64:
        hash_bit = bit - 32
        dim = 1
    elif 64<=bit and bit<80:
        hash_bit = bit - 64
        dim = 2
    elif 80<=bit and bit<96:
        hash_bit = bit - 80
        dim = 3
    elif 96<=bit and bit<104:
        hash_bit = bit - 96
        dim = 4
    rule_mask = 1<<(FIELD_LENTH[dim]-1-hash_bit)
    # get each rule's separa-state by the bit. 0:can't separa, 1:bit=0, 2:bit=1
    rule_num = len(rule_set)
    rule_state_array = [0] * rule_num
    for i, rule in enumerate(rule_set):
        if rule[dim][0] ^ rule[dim][1] >= rule_mask:
            continue
        elif rule[dim][0] & rule_mask == 0:
            rule_state_array[i] = 1;
        else:
            rule_state_array[i] = 2;
    # build the separa dict:
    separated_pairs = list()
    label = int(0)          #basic unit of the dictionary: int
    cnt = 0
    for i in range(rule_num):
        for j in range(i+1,rule_num):
            if cnt > 29:    #30 bits used per int(which takes 12 Byte memory size)
                separated_pairs.append(label)
                cnt = 0
                label = 0
            label = label << 1
            if rule_state_array[i] * rule_state_array[j] == 2:
                label = label | 1
            cnt = cnt + 1
    separated_pairs.append(label)
    return separated_pairs

# count the sum of pairs
def pair_count(pair_dict):
    result = 0
    for x in pair_dict:
        result = result + pair_per_label(x)
    return result


# count how many "1" bit in each label
def pair_per_label(x):
    m1 = 0x55555555
    m2 = 0x33333333
    m4 = 0x0f0f0f0f
    m8 = 0x00ff00ff
    m16 = 0x0000ffff
    x = (x & m1) + ((x >> 1) & m1)
    x = (x & m2) + ((x >> 2) & m2)
    x = (x & m4) + ((x >> 4) & m4)
    x = (x & m8) + ((x >> 8) & m8)
    x = (x & m16) + ((x >> 16) & m16)
    return x


# to make the subtraction between two pair_dicts
def pair_dict_sub(pair_dict1, pair_dict2):
    for i in range(len(pair_dict1)):
        pair_dict1[i] = pair_dict1[i] & (~pair_dict2[i])



if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: %s rule_set' % sys.argv[0])
        sys.exit(0)
    if len(sys.argv) == 2:
        logging.basicConfig(format='%(levelname)s: %(message)s', level=logging.INFO)
    else:
        for arg in sys.argv[2:]:
            if(arg == '--debug'):
                logging.basicConfig(format='%(levelname)s: %(message)s', level=logging.DEBUG)

    logger = logging.getLogger(__name__)
    total_leaf_number = 0
    total_leaf_depth = 0
    max_leaf_depth = 0
    total_mem_size = 0
    max_level = 0
    filename = sys.argv[1] + '_result'
    csvname = sys.argv[1] + '_PrCt.csv'
    csvname2 = sys.argv[1] + '_PrCt2.csv'
    # result_file = open(filename, 'w')
    csvfile = open(csvname, 'w')
    csvfile2 = open(csvname2, 'w')

    start_time = time.clock()
    rule_set, rule_set_text = load_rules(sys.argv[1])
    # result_file.write("toal rules: %d\n"%len(rule_set)+'*'*20+'\n') 
    bit_select_pairwise(rule_set, rule_set_text)
    end_time = time.clock()
    average_access_time = float(total_leaf_depth)/float(total_leaf_number)
    logger.info("average mem access: %f"%average_access_time)
    logger.info("worst mem access: %d"%max_leaf_depth)
    logger.info("mem size: %.2f KB"%(total_mem_size/1024.0))
    logger.info("max level: %d"%max_level)
    logger.info("Preprocessing time is %.03f ms"%((end_time - start_time)*1000))
    # result_file.write('\n'+'*'*20+'\n')
    # result_file.write("total leaf number: %d\n"%total_leaf_number)
    # result_file.write("average mem access: %f\n"%average_access_time) 
    # result_file.write("worst mem access: %d\n"%max_leaf_depth)
    # result_file.write("mem size: %.2f KB\n"%(total_mem_size/1024.0)) 
    # result_file.write("max level: %d\n"%max_level)
    # result_file.close()
    csvfile.close()
    csvfile2.close()
