#!/bin/sh
# chunks of 100 complexes, each run under nice -n 10 timeout 1200
cd "$(dirname "$0")"
for c in 52_31 52_30 51_31 51_30 50_31 50_30; do
  N=$(python3 -c "import json;print(len(json.load(open('census_$c.json'))['reps']))")
  : > out_$c.jsonl
  s=0
  while [ $s -lt $N ]; do
    nice -n 10 timeout 1200 python3 lo_census.py census_$c.json $s $((s+100)) >> out_$c.jsonl 2>> err_$c.log
    echo "$c $s exit=$?" >> run_53.log
    s=$((s+100))
  done
done
echo DONE >> run_53.log
