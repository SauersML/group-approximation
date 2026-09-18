#!/bin/bash
# usage: k5hilane.sh NSL i1 i2 ...   K5 at TARGET 7.0857 (> 45 sqrt3/11), T = 3.55; slice i of the first free
# phase theta_23 in [i (pi/2)/NSL, (i+1)(pi/2)/NSL] (symmetry reduction of the K5 node); resumable.
cd "$(dirname "$0")"
N=$1; shift
for i in "$@"; do
  lo=$(python3 -c "import math;print($i*math.pi/2/$N)"); hi=$(python3 -c "import math;print(($i+1)*math.pi/2/$N)")
  for rep in $(seq 1 60); do
    OMP_NUM_THREADS=1 nice -n 10 timeout 1200 python3 -u graphbb.py K5 7.0857 3.55 3 $lo $hi ck_k5hi_n${N}_s$i.pkl 2>&1 | grep --line-buffered -v -e Warning -e "prob.solve" >> k5hi_n${N}_s$i.log
    grep -q "ALL CLOSED\|FAIL" k5hi_n${N}_s$i.log && break
  done
done
