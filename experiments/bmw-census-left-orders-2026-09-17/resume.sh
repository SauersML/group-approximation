#!/bin/sh
# resume after container restart: finish 41_40 from 900, then 40_40, then degree (5,3)
cd "$(dirname "$0")"
run() { c=$1; s=$2; N=$(python3 -c "import json;print(len(json.load(open('census_$c.json'))['reps']))")
  while [ $s -lt $N ]; do
    nice -n 10 timeout 1200 python3 lo_census.py census_$c.json $s $((s+100)) >> out_$c.jsonl 2>> err_$c.log
    echo "$c $s exit=$?" >> $3; s=$((s+100)); done; }
run 41_40 900 run_all.log
: > out_40_40.jsonl; run 40_40 0 run_all.log; echo DONE >> run_all.log
for c in 52_31 52_30 51_31 51_30 50_31 50_30; do : > out_$c.jsonl; run $c 0 run_53.log; done
echo DONE >> run_53.log
