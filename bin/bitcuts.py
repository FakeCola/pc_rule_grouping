#!/usr/bin/env python
# -*- coding:utf-8 -*-


"""
functions for BitCuts.
"""


from __future__ import print_function

import time
from param import *
from log import g_log_inst


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
            g_log_inst.get().debug("change current node to leaf node")
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
        g_log_inst.get().debug("Current length %d bit_array: %r" % (len(bit_array),
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

        g_log_inst.get().debug("current node split finished (depth: %d)" % curr_depth)

    return max_depth, max_leaf_depth, total_leaf_number, total_leaf_depth, \
        total_mem_size



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
            g_log_inst.get().debug("bit %d : %d"%(bit, bit_pair_size[bit]))
        pair_num += bit_pair_size[bit]

    origin_rule_num = len(ruleset)
    max_bucket_size = origin_rule_num
    max_bucket_num = 1
    if pair_num == 0:
        g_log_inst.get().debug("No single bit can be selected to split")
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
            g_log_inst.get().debug("Cannot continue to split by single bit")
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
        g_log_inst.get().debug("add bit %d" % bit_selected)
        g_log_inst.get().debug("max_bucket_size %d, max_bucket_num %d" % (max_bucket_size,
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

