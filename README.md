# PC Rule Grouping

This is my graduation project @NSLab, Tsinghua.

The goal is to provide a rule grouping algorithm for packet classification (PC), to improve the PC performance.

---

The main script is `grouping.py` under `bin\` directory.

Usage: 

```sh
$ ./bin/grouping.py [-h] [-n MAX_GROUP_NUM] [-m MEMORY_SIZE] [-o OPTIMIZE_RATIO] [-s SAVE_RESULTS] [-v] <ruleset> {bitcuts,efficuts}
```

```
positional arguments:
  <ruleset>               the ruleset to load
  {bitgrouping,efficuts}    grouping algorithm selected

optional arguments:
  -h, --help            show this help message and exit
  -n MAX_GROUP_NUM, --max-group-num MAX_GROUP_NUM
                        maximum number of groups
  -m MEMORY_SIZE, --memory-size MEMORY_SIZE
                        expected memory size of data structures
  -o OPTIMIZE_RATIO, --optimize-ratio OPTIMIZE_RATIO
                        the decreasing ratio when optimize the memory size,
                        only works when --memory_size is set
  -s SAVE_RESULTS, --save-results SAVE_RESULTS
                        the file to save the group results
  -v, --verbosity       output the running log of bitcuts algorithm
```

**Note**:
Using `pypy` to accelerate.

---

e.g.

```sh
$ pypy bin/grouping.py -n 10 -m 39 -o 0.8 -s result/ipc1_1K_grp ruleset/ipc1_1K bitgrouping
```

This command will use `BitGrouping` to group the rules from ruleset `ruleset/ipc1_1K` and save the grouping result into `result/ipc1_1K_grp`. The maximum grouping number is `10`. Optimization is enabled and the memory size is expected to be smaller than `39`KB. The decreasing ratio is set to `0.8`.
