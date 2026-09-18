#!/bin/sh
# chunks of 100 complexes, each run under nice -n 10 timeout 1200
cd "$(dirname "$0")"
for c in 30_30 31_30 31_31 40_30 41_30 41_31 42_30 42_31 42_42 41_41 42_41 42_40 41_40 40_40; do
  N=$(python3 -c "import json;print(len(json.load(open('census_$c.json'))['reps']))")
  : > out_$c.jsonl
  s=0
  while [ $s -lt $N ]; do
    nice -n 10 timeout 1200 python3 lo_census.py census_$c.json $s $((s+100)) >> out_$c.jsonl 2>> err_$c.log
    echo "$c $s exit=$?" >> run_all.log
    s=$((s+100))
  done
done
echo DONE >> run_all.log
