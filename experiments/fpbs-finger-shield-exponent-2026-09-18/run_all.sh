#!/bin/sh
# Reproduces results.txt (about 2 CPU-hours in total; each run is single-threaded).
#   gcc -O2 -o theta_chain theta_chain.c -lm
#   sh run_all.sh ./theta_chain > results.txt
# Usage of the binary: theta_chain n samples seed [p]   (p defaults to 0.5)
B=${1:-./theta_chain}
# critical box proxies
for a in "16 40000 1" "32 20000 2" "64 10000 3" "128 4000 4"; do
  nice -n 10 timeout 1200 $B $a
done
# n = 256 in independent 500-sample runs (pool them)
for sd in 5 6 8 9 10 11; do
  nice -n 10 timeout 1200 $B 256 500 $sd
done
# near-critical, infinite-volume proxies (n = 128 >> L(p'))
for p in 0.56 0.60 0.66 0.75; do
  nice -n 10 timeout 1200 $B 128 1200 7 $p
done
