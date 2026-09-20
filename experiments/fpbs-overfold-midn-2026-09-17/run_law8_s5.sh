#!/bin/sh
# Completes s = 5 on inst12j1_law8.  Part 3 of 4 (P[0] index r = 3 mod 4,
# i.e. r = 3, 7 mod 8) finished s = 5 in law8_s5_p3.txt; this runs the
# remaining residues r mod 8 in {0,1,2,4,5,6}.
cd "$(dirname "$0")"
for p in 0 1 2 4 5 6; do
  nice -n 5 ./rel inst12j1_law8.txt 5 0 fast $p 8 > law8_s5_q$p.txt &
done
wait
