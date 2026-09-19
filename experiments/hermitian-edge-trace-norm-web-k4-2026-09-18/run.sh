#!/bin/bash
# usage: [SYM=...] [ROOT=r] [FIRST=i-j] run.sh TAG GRAPH TARGET T A_LO A_HI [REPS]
# repeats `nice -n 10 timeout 1200 fastbb.py GRAPH TARGET T A_LO A_HI TAG.pkl`, resuming from the checkpoint,
# until ALL CLOSED or FAIL appears in TAG.log.  Single-threaded.
cd "$(dirname "$0")"
TAG=$1; shift; R=${6:-40}
for rep in $(seq 1 $R); do
  OMP_NUM_THREADS=1 nice -n 10 timeout 1200 python3 -u fastbb.py $1 $2 $3 $4 $5 $TAG.pkl 2>&1 | grep --line-buffered -v -e Warning -e "prob.solve" >> $TAG.log
  grep -q "ALL CLOSED\|FAIL" $TAG.log && break
done
