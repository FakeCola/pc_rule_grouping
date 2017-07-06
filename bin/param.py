#!/usr/bin/env python
# -*- coding:utf-8 -*-


# packet header format
DIM_SIP, DIM_DIP, DIM_SPORT, DIM_DPORT, DIM_PROTO, DIM_MAX = range(6)
UINT32_MAX, UINT16_MAX, UINT8_MAX = ((1 << i) - 1 for i in [32, 16, 8])
DIM_POINT_MAX = [UINT32_MAX, UINT32_MAX, UINT16_MAX, UINT16_MAX, UINT8_MAX]
BIT_RANGE = [(0,31),(32,63),(64,79),(80,95),(96,103)]
FIELD_LENTH = [32, 32, 16, 16, 8]
BIT_LENGTH = 104


# memory size
NON_LEAF_BUCKET_STRUCTURE_SIZE = 13 + 4 + 4
LEAF_BUCKET_STRUCTURE_SIZE = 4
LINEAR_BUCKET_SIZE = 4


# BitCuts parameters
BINTH = 8
SPFAC = 4


# EffiCuts grouping parameters
IP_BIN_RATIO = 0.05
PORT_BIN_RATIO = 0.5
PROTO_BIN_RATIO = 1


# BitGrouping parameters
OPTIMIZE_RATIO = 0.8
MAX_REMAINED_RULES = 100
MAX_GROUP_NUM = 10
