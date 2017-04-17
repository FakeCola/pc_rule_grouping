#!/bin/bash

mkdir -p ./log

log_dir=./log
log_file=${log_dir}/rule_repli.log

rm -f $log_file

for ruleset_size in 1K 5K 10K; do
    for ruleset in acl1 fw1 ipc1; do
        echo "*** ${ruleset}_${ruleset_size}***" >> $log_file
        pypy bitcuts.py ruleset/${ruleset}_${ruleset_size} >> $log_file
    done
done
