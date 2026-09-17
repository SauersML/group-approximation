#!/bin/sh
# Reproduce the annealing table: best breakpoint ratio B/n found for f^K = id, K = 2,3,4.
# K = 2 and K = 3 are calibration cases where the ratio is provably bounded below (trivial covers).
# Build: cc -O2 -o anneal anneal_breakpoints.c -lm
set -e
cd "$(dirname "$0")"
[ -x ./anneal ] || cc -O2 -o anneal anneal_breakpoints.c -lm
: > anneal_results.txt
for n in 101 301 1001 3001; do
  steps=$((20000 * n)); [ $steps -gt 60000000 ] && steps=60000000
  for K in 2 3 4; do
    nice -n 10 timeout 1200 ./anneal $n $K $steps 1 1 >> anneal_results.txt
  done
done
cat anneal_results.txt
