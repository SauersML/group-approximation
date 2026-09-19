#!/bin/bash
# usage: weblane.sh GRAPH TARGET T TAG [A_LO A_HI]  -- runs graphbb.py GRAPH TARGET T 3 A_LO A_HI (first free
# phase in [A_LO, A_HI], default [0, 2pi]), resuming from ck_TAG.pkl after each 1200 s try; appends to TAG.log
cd "$(dirname "$0")"
G=$1; TG=$2; T=$3; TAG=$4; LO=${5:-0}; HI=${6:-6.283185307179586}
for rep in $(seq 1 60); do
  OMP_NUM_THREADS=1 nice -n 10 timeout 1200 python3 -u graphbb.py $G $TG $T 3 $LO $HI ck_$TAG.pkl 2>&1 | grep --line-buffered -v -e Warning -e "prob.solve" >> $TAG.log
  grep -q "ALL CLOSED\|FAIL" $TAG.log && break
done
