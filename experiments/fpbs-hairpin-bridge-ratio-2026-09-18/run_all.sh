#!/bin/sh
# Reproduce results.txt.  Single-threaded; each command well under 20 minutes on an idle core.
set -e
D=$(dirname "$0")
cc -O2 -o /tmp/hairpin "$D/hairpin.c" -lm
cc -O2 -o /tmp/kpattern "$D/kpattern.c" -lm
# exact column environment (rigorous side: transfer, brute force, closed forms)
python3 "$D/exact_column.py" > "$D/exact_column.txt"
# (1) direct Br/TJT and n D_n, hairpin vs straight, percolation spine (box proxy)
for t in 1 0; do nice -n 10 timeout 1200 /tmp/hairpin $t 30 0.55 0.2 12 20000 2; done
# (2) middle-split excess Lmid(n): cross-fold coverage correlation of the two arms
for n in 22 42 82 162; do for t in 1 0; do
  nice -n 10 timeout 1200 /tmp/hairpin $t $n 0.55 0.5 12 40000 3 1
done; done
for p in 0.55 0.6 0.7; do for t in 1 0; do
  nice -n 10 timeout 1200 /tmp/hairpin $t 22 $p 0.3 12 40000 3 1
done; done
for t in 1 0; do nice -n 10 timeout 1200 /tmp/hairpin $t 22 0.6 0.5 12 40000 3 1; done
# (3) matched multi-run pattern: log K(S) for l runs per side
for l in 2 4 8 16; do for t in 1 0; do
  nice -n 10 timeout 1200 /tmp/kpattern $t $l 0.55 12 40000 4
done; done
