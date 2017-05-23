#!/usr/bin/env python

from __future__ import print_function

import re
import sys
import copy
import collections
import logging
import time
import itertools
import argparse


DIM_SIP, DIM_DIP, DIM_SPORT, DIM_DPORT, DIM_PROTO, DIM_MAX = range(6)
UINT32_MAX, UINT16_MAX, UINT8_MAX = ((1 << i) - 1 for i in [32, 16, 8])
DIM_POINT_MAX = [UINT32_MAX, UINT32_MAX, UINT16_MAX, UINT16_MAX, UINT8_MAX]

BIT_RANGE = [(0,31),(32,63),(64,79),(80,95),(96,103)]
FIELD_LENTH = [32, 32, 16, 16, 8]
BIT_LENGTH = 104
BINTH = 8
SPFAC = 4


stat = {}

NON_LEAF_BUCKET_STRUCTURE_SIZE = 13 + 4 + 4
LEAF_BUCKET_STRUCTURE_SIZE = 4
LINEAR_BUCKET_SIZE = 4


# EffiCuts grouping parameter
IP_BIN_RATIO = 0.05
PORT_BIN_RATIO = 0.5
PROTO_BIN_RATIO = 1

# BitCuts grouping parameter
OPTIMIZE_RATIO = 0.8
MAX_REMAINED_RULES = 100
MAX_GROUP_NUM = 10

# rule format:
# [[sip_begin, sip_end, sip_mask_len], [dip_begin, dip_end, dip_mask_len] ...,
# [proto_begin, proto_end], [pri]]
def load_ruleset(ruleset_fname):
    ruleset = []
    ruleset_text = []
    rule_fmt = re.compile(r'^@(\d+).(\d+).(\d+).(\d+)/(\d+) '
            r'(\d+).(\d+).(\d+).(\d+)/(\d+) '
            r'(\d+) : (\d+) '
            r'(\d+) : (\d+) '
            r'(0x[\da-fA-F]+)/(0x[\da-fA-F]+)$')

    for idx, line in enumerate(open(ruleset_fname)):
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

        ruleset.append([[sip_begin, sip_end, sip_mask_len],
            [dip_begin, dip_end, dip_mask_len],
            [sport_begin, sport_end], [dport_begin, dport_end],
            [proto_begin, proto_end], [idx]])
        ruleset_text.append(line)

    return ruleset,ruleset_text


# Split the rule set into buckets according to the bit_array. Each bucket
# contains a subset of rules.
def split_ruleset(ruleset, bit_array):
    buckets = [[] for i in range(1 << len(bit_array))]
    for r in ruleset:
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
    bucket_percentage_stat = {size:(float(num)/float(len(buckets)))
        for size, num in bucket_size_stat.iteritems()}
    return buckets, max_bucket_size, max_bucket_num, bucket_percentage_stat


# Called by split_ruleset, decides which bucket a rule belongs to given the
# bit array
def split_rule(rule, bit_array, buckets):
    bit_array_len = len(bit_array)
    for index in range(1 << bit_array_len):
        index_in = 1
        for i, bit in enumerate(bit_array):
            index_mask = 1 << (bit_array_len-1-i)
            if 0 <= bit and bit < 32:
                hash_bit = bit
                rule_mask = 1 << (31-hash_bit)
                if hash_bit+1 <= rule[0][2]:
                    if ((index&index_mask) >> (bit_array_len-1-i)) != (
                        (rule[0][0]&rule_mask) >> (31-hash_bit)):
                        index_in = 0
                        break
            elif 32 <= bit and bit < 64:
                hash_bit = bit - 32
                rule_mask = 1 << (31-hash_bit)
                if hash_bit+1 <= rule[1][2]:
                    if ((index&index_mask) >> (bit_array_len-1-i)) != (
                        (rule[1][0]&rule_mask) >> (31-hash_bit)):
                        index_in = 0
                        break
            elif 64 <= bit and bit < 80:
                hash_bit = bit - 64
                rule_mask = 1 << (15-hash_bit)
                if rule_mask > rule[2][1]-rule[2][0]:
                    port_xor = rule[2][1]^rule[2][0]
                    if (port_xor&rule_mask) == 0:
                        if (index&index_mask) >> (bit_array_len-1-i) != (
                            rule[2][0]&rule_mask) >> (15-hash_bit):
                            index_in = 0
                            break
            elif 80 <= bit and bit < 96:
                hash_bit = bit - 80
                rule_mask = 1 << (15-hash_bit)
                if rule_mask > rule[3][1]-rule[3][0]:
                    port_xor = rule[3][1]^rule[3][0]
                    if (port_xor&rule_mask) == 0:
                        if (index&index_mask) >> (bit_array_len-1-i) !=(
                            rule[3][0]&rule_mask) >> (15-hash_bit):
                            index_in = 0
                            break
            elif 96 <= bit and bit < 104:
                hash_bit = bit - 96
                rule_mask = 1 << (7-hash_bit)
                if rule[4][1]-rule[4][0] != 255:
                    if (index&index_mask) >> (bit_array_len-1-i) != (
                        rule[4][0]&rule_mask) >> (7-hash_bit):
                        index_in = 0
                        break
        if index_in == 1:
            buckets[index].append(rule)


# Recursively build the BitCuts tree.
# calculate necessary metrics (memory access time, memory size, etc)
def build_tree(ruleset, ruleset_text):
    # basic matrics
    max_depth = 0
    max_leaf_depth = 0
    total_leaf_number = 0
    total_leaf_depth = 0
    total_mem_size = 0
    # node format: [tree-depth, parent-bit-array, msg]
    node_stack = []
    node_stack.append([0, [], ruleset, ''])  # root node

    while len(node_stack):
        curr_depth, parent_bit_array, curr_ruleset, curr_msg = node_stack.pop()

        if curr_depth > max_depth:
            max_depth = curr_depth
        avaliable_bit_array = list(set(range(BIT_LENGTH))-set(parent_bit_array))

        if curr_depth == 0:
            verbose = True
        else:
            verbose = False
        bit_array, further_separable, split_info = bit_select(curr_ruleset,
            avaliable_bit_array, verbose=verbose)

        # if current non-leaf node cannnot be further splitted, turn it into
        # leaf node
        if not len(bit_array):
            logger.debug("change current node to leaf node")
            #for j, r in enumerate(curr_ruleset):
            #    if j == 0:
            #        result_file.write('\t' * level + new_msg + str(i) + ': ' + ruleset_text[r[DIM_MAX][0]][:-1] + '\n')
            #    else:
            #        result_file.write('\t' * level + len(new_msg + str(i) + ': ') * ' ' + ruleset_text[r[DIM_MAX][0]][:-1] + '\n')
            total_leaf_number += 1
            total_leaf_depth += curr_depth + len(curr_ruleset)
            if max_leaf_depth < curr_depth + len(curr_ruleset):
                max_leaf_depth = curr_depth + len(curr_ruleset)
            # append memory cost for storing the rules
            total_mem_size += len(curr_ruleset) * LINEAR_BUCKET_SIZE
            continue

        buckets, max_bucket_size, max_bucket_num, bucket_percentage_stat = \
            split_info
        if curr_depth == 0:
            #result_file.write("Basic bit array: %r\n\n" % bit_array)
            new_msg = curr_msg
        else:
            new_msg = curr_msg + str(bit_array) + '-'
        bit_array = bit_array + parent_bit_array
        logger.debug("Current length %d bit_array: %r" % (len(bit_array),
            bit_array))


        # If rule-num of every bucket is no more than BINTH, it means every
        # bucket will become leaf node. Then this level will be regarded as a
        # bottom level
        if max_bucket_size <= BINTH:
            bottom_level = True
        else:
            bottom_level = False

        # next level
        for idx, subset in enumerate(buckets):
            # Non-leaf node
            if len(subset) > BINTH and further_separable == True:
                total_mem_size += NON_LEAF_BUCKET_STRUCTURE_SIZE
                #result_file.write('\t' * curr_depth + new_msg + str(idx)
                #    + ': \n')
                node_stack.append([curr_depth + 1, bit_array, subset, new_msg])
            # Leaf node
            else:
                #if subset:
                #    for j, r in enumerate(subset):
                #        if j == 0:
                #            result_file.write('\t' * level + new_msg + str(i) + ': ' + ruleset_text[r[DIM_MAX][0]][:-1] + '\n')
                #        else:
                #            result_file.write('\t' * level + len(new_msg + str(i) + ': ') * ' ' + ruleset_text[r[DIM_MAX][0]][:-1] + '\n')
                total_leaf_number += 1
                total_leaf_depth += curr_depth + 2 + len(subset)
                if max_leaf_depth < curr_depth + 2 + len(subset):
                    max_leaf_depth = curr_depth + 2 + len(subset)
                if bottom_level == True:
                    total_mem_size += LEAF_BUCKET_STRUCTURE_SIZE + len(subset) \
                        * LINEAR_BUCKET_SIZE
                else:
                    total_mem_size += NON_LEAF_BUCKET_STRUCTURE_SIZE + \
                        len(subset) * LINEAR_BUCKET_SIZE

        logger.debug("current node split finished (depth: %d)" % curr_depth)

    return max_depth, max_leaf_depth, total_leaf_number, total_leaf_depth, \
        total_mem_size


def grouping_optimize(ruleset, ruleset_text, memory_boundary,
    max_group_num=float('inf')):
    separable_rulesets = []
    unseparable_rulesets = [ruleset]  # for further grouping
    group_idx = 0
    grouping_bias = [0]
    grouping_mem = []
    exhausted_idx = 0  # group_idx before which cannot further be adjusted
    while group_idx < max_group_num:
        print("--  Group %d  --" % group_idx)

        (subset1, subset2), is_exhausted = one_level_tree_grouping(
            unseparable_rulesets[-1], grouping_bias[-1])

        # check whether exhausted:
        if is_exhausted and exhausted_idx == group_idx:
            exhausted_idx += 1

        max_depth1, max_leaf_depth1, total_leaf_number1, total_leaf_depth1, \
            total_mem_size1 = build_tree(subset1, ruleset_text)
        avg_access_time1 = float(total_leaf_depth1) / float(total_leaf_number1)
        print("Tree1 : max_depth=%d, max_leaf_depth=%d, avg_access_time=%f, "
              "total_mem_size=%f KB" % (max_depth1, max_leaf_depth1,
              avg_access_time1, total_mem_size1/1024.0))
        separable_rulesets.append(subset1)

        # backtrack when memory exceeds threshold
        grouping_mem.append(total_mem_size1)
        if sum(grouping_mem) > memory_boundary:
            if group_idx >= exhausted_idx:
                print("Memory exceeds threshold!")
                backtracking_idx = grouping_bias[exhausted_idx:].index(
                    grouping_bias[-1]) + exhausted_idx
                group_idx = backtracking_idx
                print("==> Backtracking to group %d" % group_idx)
                separable_rulesets = separable_rulesets[:group_idx]
                unseparable_rulesets = unseparable_rulesets[:group_idx+1]
                grouping_bias = grouping_bias[:group_idx+1]
                grouping_bias[-1] += 1
                grouping_mem = grouping_mem[:group_idx]
                continue
            else:
                # unable to reach the goal
                print("failed to decrease the memory size to smaller than given"
                    " value")
                return False, None, -1

        max_depth2, max_leaf_depth2, total_leaf_number2, total_leaf_depth2, \
            total_mem_size2 = build_tree(subset2, ruleset_text)
        avg_access_time2 = float(total_leaf_depth2) / float(total_leaf_number2)
        print("Tree2 : max_depth=%d, max_leaf_depth=%d, avg_access_time=%f, "
              "total_mem_size=%f KB" % (max_depth2, max_leaf_depth2,
              avg_access_time2, total_mem_size2/1024.0))
        unseparable_rulesets.append(subset2)

        group_idx += 1
        total_grouping_mem = sum(grouping_mem) + total_mem_size2
        if total_grouping_mem < memory_boundary:
            break
        grouping_bias.append(0)

    grouped_rulesets = separable_rulesets + [unseparable_rulesets[-1]]
    print("--  grouping result  --")
    print("grouping bias: %s" % grouping_bias)
    print("ruleset nums: %s" % map(len, grouped_rulesets))
    print("total memory size: %.3f KB" % (total_grouping_mem/1024.0))
    return True, grouped_rulesets, total_grouping_mem


def grouping_base(ruleset, ruleset_text, max_group_num=float('inf'),
    max_remained_rules=MAX_REMAINED_RULES):
    grouped_rulesets = []
    subset2 = ruleset # for further grouping
    group_idx = 0
    while group_idx < max_group_num:
        print("--  Group %d  --" % group_idx)
        (subset1, subset2), _ = one_level_tree_grouping(subset2)
        grouped_rulesets.append(subset1)
        group_idx += 1
        if len(subset2) < max_remained_rules:
            break
    grouped_rulesets.append(subset2)
    print("--  grouping result  --")
    print("ruleset nums: %s" % map(len, grouped_rulesets))
    return grouped_rulesets


def one_level_tree_grouping(ruleset, bias=0):
    # build one-level tree
    bit_array, _, split_info = bit_select(ruleset, range(BIT_LENGTH),
        use_spfac=True, verbose=True)
    buckets, max_bucket_size, max_bucket_num, _ = split_info

    # count replication
    rule_ref = []
    for bucket in buckets:
        rule_ref.extend(map(lambda r: r[DIM_MAX][0], bucket))
    rule_ref_cnt = dict(collections.Counter(rule_ref))
    rule_ref_dstr = collections.Counter(rule_ref_cnt.values())
    rule_ref_avg = sum(k * v for k, v in rule_ref_dstr.items()
                       ) / float(sum(rule_ref_dstr.values()))

    # split the ruleset
    rule_ref_thres = rule_ref_avg / (2.0 ** bias)
    subset1 = []
    subset2 = []
    for rule in ruleset:
        rule_id = rule[DIM_MAX][0]
        if rule_ref_cnt[rule_id] > rule_ref_thres:
            subset2.append(rule)
        else:
            subset1.append(rule)

    is_exhausted = False
    if rule_ref_thres / 2.0 < min(rule_ref_dstr.keys()):
        is_exhausted = True

    print("bit selected: %s" % bit_array)
    print("ref distribution: %s" % dict(rule_ref_dstr))
    print("avg ref: %f, threshold: %f" % (rule_ref_avg, rule_ref_thres))
    print("subset1: %d, subset2: %d" % (len(subset1), len(subset2)))
    return (subset1, subset2), is_exhausted


# grouping algorithm by efficuts
def grouping_efficuts(ruleset, ruleset_text):
    # initialization
    largeness_fraction = [IP_BIN_RATIO, IP_BIN_RATIO, PORT_BIN_RATIO,
                          PORT_BIN_RATIO, PROTO_BIN_RATIO]
    assert len(largeness_fraction) == DIM_MAX, ("largeness fraction of each "
        "dimension should be assigned")
    big_rules = [[] for _ in range(5)]
    kinda_big_rules = [[] for _ in range(10)]
    medium_rules = [[] for _ in range(10)]
    small_rules = []
    fields = [0] * DIM_MAX
    # get combinations of 2 wildcard fields and 3 wildcard fields
    wild3_dict = {bin_id: set(comb) for bin_id, comb in enumerate(
        itertools.combinations(range(DIM_MAX), 2))}
    wild2_dict = {bin_id: set(comb) for bin_id, comb in enumerate(
        itertools.combinations(range(DIM_MAX), 3))}

    # grouping by non-wildcard fields
    for rule in ruleset:
        small_fields = []
        for dim in range(DIM_MAX):
            fields[dim] = rule[dim][1] - rule[dim][0]
            if fields[dim] < DIM_POINT_MAX[dim] * largeness_fraction[dim]:
                small_fields.append(dim)
        wild_field_num = DIM_MAX - len(small_fields)
        if wild_field_num == 5:
            big_rules[fields.index(min(fields[:-1]))].append(rule)
        elif wild_field_num == 4:
            big_rules[small_fields[0]].append(rule)
        elif wild_field_num == 3:
            small_fields_set = set(small_fields)
            for bin_id, comb_set in wild3_dict.iteritems():
                if comb_set == small_fields_set:
                    kinda_big_rules[bin_id].append(rule)
                    break
        elif wild_field_num == 2:
            small_fields_set = set(small_fields)
            for bin_id, comb_set in wild2_dict.iteritems():
                if comb_set == small_fields_set:
                    medium_rules[bin_id].append(rule)
                    break
        else:  # wild_field_num <= 1
            small_rules.append(rule)

    # sort grouping result
    grouped_rulesets = [0] * 26
    grouped_rulesets[:5] = big_rules
    grouped_rulesets[5:15] = kinda_big_rules
    grouped_rulesets[15:25] = medium_rules
    grouped_rulesets[-1] = small_rules
    ruleset_flag = map(lambda x: 1 if len(x) > 0 else 0, grouped_rulesets)
    print("--  before merge  --")
    print("group nums: %d" % sum(ruleset_flag))
    print("ruleset nums:\n %s" % map(len, grouped_rulesets))
    print("ruleset flags:\n %s" % ruleset_flag)

    # merge
    merging_efficuts(grouped_rulesets, ruleset_flag)
    print("--  after merge  --")
    print("group nums: %d" % sum(ruleset_flag))
    print("ruleset nums:\n %s" % map(len, grouped_rulesets))
    print("ruleset flags:\n %s" % ruleset_flag)

    # final groups
    grouped_rulesets = filter(lambda x: len(x), grouped_rulesets)
    print("--  grouping result  --")
    print("ruleset nums: %s" % map(len, grouped_rulesets))

    return grouped_rulesets


def merging_efficuts(grouped_rulesets, ruleset_flag):
    merged = [False] * len(grouped_rulesets)
    # get merge order
    merge_dict = dict()
    wild3_combinations = list(itertools.combinations(range(5), 2))
    for i in range(5):
        merge_dict[i] = map(lambda x: x+5, filter(
            lambda x: i in wild3_combinations[x],
            range(len(wild3_combinations))))
    wild2_combinations = list(itertools.combinations(range(5), 3))
    for i, wild3_comb_set in enumerate(map(set, wild3_combinations)):
        merge_dict[i+5] = map(lambda x: x+15, filter(
            lambda x: len(wild3_comb_set - set(wild2_combinations[x])) == 0,
            range(len(wild2_combinations))))
    # start merging
    print("--  merge info  --")
    for idx in range(5) + range(5, 15)[::-1]:
        if ruleset_flag[idx] == 1:
            for i in merge_dict[idx][::-1]:
                if ruleset_flag[i] == 1 and not merged[i]:
                    grouped_rulesets[idx].extend(grouped_rulesets[i])
                    grouped_rulesets[i] = []
                    ruleset_flag[i] = 0
                    merged[idx] = True
                    print("group %d is merged to group %d" % (i, idx))
                    break



def bit_select(ruleset, avaliable_bit_array, max_bit_array_length=float('inf'),
    use_spfac=True, verbose=False):
    # format: {bit: pair_dict}. Here pair_dict is the dictionary of rule
    # pairs. All the pairs this bit can separate are set to 1
    bit_pair_dict = {}
    bit_pair_size = {}  # format: {bit: pair_size}
    pair_num = 0

    # get pair info
    for bit in avaliable_bit_array:
        bit_pair_dict[bit] = bit_separation_info(ruleset, bit)
        bit_pair_size[bit] = pair_count(bit_pair_dict[bit])
        if verbose:
            logger.debug("bit %d : %d"%(bit, bit_pair_size[bit]))
        pair_num += bit_pair_size[bit]

    origin_rule_num = len(ruleset)
    max_bucket_size = origin_rule_num
    max_bucket_num = 1
    if pair_num == 0:
        logger.debug("No single bit can be selected to split")
        return [], False, []

    # select cutting bits
    bit_array = []
    further_separable = True
    while max_bucket_size > 1:
        # select the best bit in terms of "separability":
        sorted_bit_pair_size = sorted(bit_pair_size.items(),
            key=lambda x:x[1], reverse=True)
        # to prevent to be stucked
        if sorted_bit_pair_size[0][1] == 0:
            logger.debug("Cannot continue to split by single bit")
            further_separable = False
            break
        bit_selected = sorted_bit_pair_size[0][0]
        bit_array.append(bit_selected)

        # update the pair-dict
        for bit, bit_pair in bit_pair_dict.iteritems():
            if bit != bit_selected:
                pair_dict_sub(bit_pair_dict[bit],
                    bit_pair_dict[bit_selected])
                bit_pair_size[bit] = pair_count(bit_pair_dict[bit])
        del bit_pair_dict[bit_selected]
        del bit_pair_size[bit_selected]
        buckets, max_bucket_size, max_bucket_num, bucket_percentage_stat = \
            split_ruleset(ruleset, bit_array)
        logger.debug("add bit %d" % bit_selected)
        logger.debug("max_bucket_size %d, max_bucket_num %d" % (max_bucket_size,
            max_bucket_num))

        # Spfac calculate
        children_rule_num = 0
        children_node_num = 2 ** len(bit_array)
        for (k, v) in bucket_percentage_stat.items():
            children_rule_num += k * v * children_node_num
        Spfac = (children_rule_num + children_node_num) / float(
            origin_rule_num)
        # Stopping criteria
        if len(bit_array) >= max_bit_array_length:
            break
        if use_spfac and Spfac > SPFAC:
            break

    split_info = (buckets, max_bucket_size, max_bucket_num,
                  bucket_percentage_stat)
    return bit_array, further_separable, split_info


# Generate bit separation information of the bit
# mark all the pairs the bit can separate in a pair dictionary and
# put the dictionary into bit_info
def bit_separation_info(ruleset, bit):
    # locate the dim and get the rule_mask
    if 0 <= bit and bit < 32:
        hash_bit = bit
        dim = 0
    elif 32 <= bit and bit < 64:
        hash_bit = bit - 32
        dim = 1
    elif 64 <= bit and bit < 80:
        hash_bit = bit - 64
        dim = 2
    elif 80 <= bit and bit < 96:
        hash_bit = bit - 80
        dim = 3
    elif 96 <= bit and bit < 104:
        hash_bit = bit - 96
        dim = 4
    rule_mask = 1 << (FIELD_LENTH[dim]-1-hash_bit)
    # get each rule's separa-state by the bit. 0:can't separa, 1:bit=0, 2:bit=1
    rule_num = len(ruleset)
    rule_state_array = [0] * rule_num
    for i, rule in enumerate(ruleset):
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
            if rule_state_array[i] + rule_state_array[j] == 3:
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


def build_multiple_trees(grouped_rulesets, ruleset_text):
    total_worst_mem_access = 0
    total_avg_mem_access = 0
    total_memory_size = 0

    print("\n====>  building tree started")
    start_time = time.clock()
    for tree_idx, r_set in enumerate(grouped_rulesets):
        print("--  tree %d  --" % tree_idx)
        max_depth, max_leaf_depth, total_leaf_number, total_leaf_depth, \
            total_mem_size = build_tree(r_set, ruleset_text)
        avg_access_time = float(total_leaf_depth)/float(total_leaf_number)
        total_worst_mem_access += max_leaf_depth
        total_avg_mem_access += avg_access_time
        total_memory_size += total_mem_size
        print("avg mem access: %f"%avg_access_time)
        print("worst mem access: %d"%max_leaf_depth)
        print("mem size: %.2f KB"%(total_mem_size/1024.0))
        print("max tree depth: %d"%max_depth)
        print("rule nums: %d" % len(r_set))
    end_time = time.clock()
    print("====>  building tree finished")

    print("total avg mem access: %f"%total_avg_mem_access)
    print("total worst mem access: %d"%total_worst_mem_access)
    print("total mem size: %.2f KB"%(total_memory_size/1024.0))
    print("====>  building time: %.03f s\n"%(end_time - start_time))

    return total_memory_size


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Script to evaluate grouping "
        "algorithms")
    parser.add_argument("ruleset", help="the ruleset to load")
    parser.add_argument("algorithm", type=str, choices=['bitcuts', 'efficuts'],
                        help="grouping algorithm selected")
    parser.add_argument("-n", "--max_group_num", default=MAX_GROUP_NUM,
                        type=int, help="maximum number of groups")
    parser.add_argument("-m", "--memory_size", type=float,
                        help="expected memory size of data structures")
    parser.add_argument("-o", "--optimize_ratio", type=float, help="the "
            "decreasing ratio when optimize the memory size, only works when "
            "--memory_size is set", default=OPTIMIZE_RATIO)
    parser.add_argument("-v", "--verbosity", action="store_true",
                        help="output the running log of bitcuts algorithm")
    args = parser.parse_args()

    if args.verbosity:
        logging.basicConfig(format='%(levelname)s: %(message)s',
            level=logging.DEBUG)
    else:
        logging.basicConfig(format='%(levelname)s: %(message)s',
            level=logging.INFO)

    logger = logging.getLogger(__name__)

    ruleset, ruleset_text = load_ruleset(args.ruleset)

    print("====>  grouping started")
    start_time = time.clock()
    if args.algorithm == 'bitcuts':
        grouped_rulesets = grouping_base(ruleset, ruleset_text,
            args.max_group_num)
    elif args.algorithm == 'efficuts':
        grouped_rulesets = grouping_efficuts(ruleset, ruleset_text,
            args.max_group_num)
    end_time = time.clock()
    print("====>  grouping finished")
    print("====>  grouping time: %.03f s"%(end_time - start_time))

    mem_baseline = build_multiple_trees(grouped_rulesets, ruleset_text)
    if args.memory_size is not None:
        args.memory_size *= 1024
        print("Considering memory size...")

        print("====>  optimizing started")
        curr_mem = mem_baseline
        while curr_mem > args.memory_size:
            while mem_baseline >= curr_mem:
                mem_baseline *= args.optimize_ratio
            mem_baseline = max([mem_baseline, args.memory_size])
            print("\n---> mem_boundary: %.3f KB\n" % (mem_baseline/1024.0))
            succeed, new_grouped_rulesets, curr_mem = grouping_optimize(ruleset,
                ruleset_text, mem_baseline, args.max_group_num)
            if not succeed:
                break
            grouped_rulesets = new_grouped_rulesets
        print("====>  optimizing finished")

        build_multiple_trees(grouped_rulesets, ruleset_text)
