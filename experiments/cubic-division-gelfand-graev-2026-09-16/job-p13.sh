#!/bin/bash
# job-p13.sh -- p = 13 (smallest prime split in K = Q(2cos 2pi/7), 3 | p - 1):
# all three Gelfand--Graev sectors (a index 1..3) and the vector sector (a = 0),
# arithmetic pair (ctl 0), B = random conjugate of A (ctl 1, two seeds), Haar-random pair (ctl 2, two seeds).
# Single-threaded, sequential, each run capped at 10 minutes.
S=/tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/gg-swarm
U="0 1 -1 0 -1 -1 -1 -1 -1"
for a in 0 1 2 3; do
  timeout 600 $S/gg run 13 $U 19 0 $a 1000 13
  for s in 1 2; do
    timeout 600 $S/gg run 13 $U 19 1 $a 1000 $s
    timeout 600 $S/gg run 13 $U 19 2 $a 1000 $s
  done
done
echo DONE
