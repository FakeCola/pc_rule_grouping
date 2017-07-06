#!/bin/bash

mkdir -p ./log

log_dir=./log
log_file=${log_dir}/effi_grouping.log
group_file=./ruleset_grp

rm -f $log_file

for ruleset_size in 1K 5K 10K; do
  for ruleset in acl1 fw1 ipc1; do
    echo "==================================================" >> $log_file
    echo "============   ${ruleset}_${ruleset_size}" >> $log_file
    echo "==================================================" >> $log_file
    echo "" >> $log_file
    for algorithm in efficuts; do
      echo "===========>   ${algorithm}" >> $log_file
      echo "" >> $log_file
      pypy bin/grouping.py ruleset/${ruleset}_${ruleset_size} $algorithm \
          -s ${group_file}/${ruleset}_${ruleset_size}_ec >> $log_file
      echo "" >> $log_file
    done
    echo "" >> $log_file
  done
done
