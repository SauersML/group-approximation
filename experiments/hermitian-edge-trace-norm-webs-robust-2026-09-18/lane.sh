#!/bin/bash
# usage: lane.sh GRAPH TARGET T N0 TAG [A_LO A_HI] -- runs graphbb_r.py, resuming from ck_TAG.pkl after each 1200 s try
cd "$(dirname "$0")"
G=$1; TG=$2; T=$3; N0=$4; TAG=$5; LO=${6:-0}; HI=${7:-6.283185307179586}
for rep in $(seq 1 200); do
  OMP_NUM_THREADS=1 nice -n 10 timeout 1200 python3 -u graphbb_r.py $G $TG $T $N0 $LO $HI ck_$TAG.pkl 2>&1 | grep --line-buffered -v -e Warning -e "prob.solve" >> $TAG.log
  grep -q "ALL CLOSED\|FAIL" $TAG.log && break
done
