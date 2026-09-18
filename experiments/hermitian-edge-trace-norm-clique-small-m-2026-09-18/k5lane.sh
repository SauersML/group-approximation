#!/bin/bash
# usage: k5lane.sh NSL i1 i2 ...  (slice i covers first phase in [i (pi/2)/NSL, (i+1)(pi/2)/NSL]); resumable
cd "$(dirname "$0")"
N=$1; shift
for i in "$@"; do
  lo=$(python3 -c "import math;print($i*math.pi/2/$N)"); hi=$(python3 -c "import math;print(($i+1)*math.pi/2/$N)")
  for rep in $(seq 1 30); do
    OMP_NUM_THREADS=1 nice -n 10 timeout 1200 python3 -u cliquebb.py 5 $lo $hi n${N}s$i 3 ck_n${N}_s$i.pkl 2>&1 | grep --line-buffered -v -e Warning -e "prob.solve" >> k5_n${N}_s$i.log
    grep -q "ALL CLOSED\|FAIL" k5_n${N}_s$i.log && break
  done
done
