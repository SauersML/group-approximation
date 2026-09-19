#!/bin/sh
# Reproduce the cascade runs.  Usage: sh run_all.sh BINARY
# (compile first: gcc -O2 -o BINARY cascade.c)
B=${1:-./cascade}
D=$(dirname "$0")
for cls in law lev0 over all; do
  $B $D/model_j1.txt 20000 1 rand $cls 0 2 > $D/rand_n20000_j1_$cls.txt
done
for cls in law over all; do
  $B $D/model_j2.txt 5000 2 rand $cls 0 2 > $D/rand_n5000_j2_$cls.txt
done
for cls in law all; do
  $B $D/model_j1.txt 1000 3 greedy $cls 300 > $D/greedy_n1000_j1_$cls.txt
done
