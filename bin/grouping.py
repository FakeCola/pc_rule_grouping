#!/usr/bin/env python
# -*- coding:utf-8 -*-

from __future__ import print_function

import re
import sys
import copy
import collections
import logging
import time
import itertools
import argparse
from param import *
from bitcuts import *
from log import *



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
        ruleset_text.append(line.strip() + " %d" % idx) # add priority

    return ruleset,ruleset_text




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




def save_group_results(grouped_rulesets, ruleset_text, fname):
    with open(fname, 'w') as fout:
        for tree_idx, r_set in enumerate(grouped_rulesets):
            print("#%d,%d" % (tree_idx, len(r_set)), file=fout)
            for r in r_set:
                print(ruleset_text[r[DIM_MAX][0]], file=fout)
        print("====> group results saved")



if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Script to evaluate grouping "
        "algorithms")
    parser.add_argument("ruleset", help="the ruleset to load")
    parser.add_argument("algorithm", type=str, choices=['bitgrouping',
                        'efficuts'], help="grouping algorithm selected")
    parser.add_argument("-n", "--max-group-num", default=MAX_GROUP_NUM,
                        type=int, help="maximum number of groups")
    parser.add_argument("-m", "--memory-size", type=float,
                        help="expected memory size of data structures")
    parser.add_argument("-o", "--optimize-ratio", type=float, help="the "
            "decreasing ratio when optimize the memory size, only works when "
            "--memory_size is set", default=OPTIMIZE_RATIO)
    parser.add_argument("-s", "--save-results", type=str, help="the file to "
            "save the group results")
    parser.add_argument("-v", "--verbosity", action="store_true",
                        help="output the running log of bitcuts algorithm")
    args = parser.parse_args()

    if args.verbosity:
        g_log_inst.start('../log/grouping.log', __name__, 'DEBUG')
    else:
        g_log_inst.start('../log/grouping.log', __name__, 'INFO')


    ruleset, ruleset_text = load_ruleset(args.ruleset)

    print("====>  grouping started")
    start_time = time.clock()
    if args.algorithm == 'bitgrouping':
        grouped_rulesets = grouping_base(ruleset, ruleset_text,
            args.max_group_num)
    elif args.algorithm == 'efficuts':
        grouped_rulesets = grouping_efficuts(ruleset, ruleset_text)
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

    if args.save_results is not None:
        save_group_results(grouped_rulesets, ruleset_text, args.save_results)
