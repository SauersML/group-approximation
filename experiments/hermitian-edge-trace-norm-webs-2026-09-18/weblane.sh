#!/bin/bash
# usage: weblane.sh GRAPH TARGET T TAG   -- runs graphbb.py GRAPH TARGET T 3 over the full first-phase range, resumable
cd "$(dirname "$0")"
G=$1; TG=$2; T=$3; TAG=$4
for rep in $(seq 1 40); do
  OMP_NUM_THREADS=1 nice -n 10 timeout 1200 python3 -u graphbb.py $G $TG $T 3 0 6.283185307179586 ck_$TAG.pkl 2>&1 | grep --line-buffered -v -e Warning -e "prob.solve" >> $TAG.log
  grep -q "ALL CLOSED\|FAIL" $TAG.log && break
done
