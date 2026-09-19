#!/bin/sh
# Triangular-lattice site percolation at p=1/2; nested boxes n=8..N on one configuration.
# pinch=1: circuit event (analogue of the Z^2 box event D_n with pinch walls).
# pinch=0: hole event (no CLE_6 hull loop meets both the negative axis and x>0).
set -e
cd "$(dirname "$0")"
gcc -O2 -o tri_d tri_d.c
mkdir -p runs
# output is flushed per sample; a timeout keeps the samples already written
nice -n 10 timeout 1200 ./tri_d 512 3000 11 1 > runs/pinch1_N512.txt || true
nice -n 10 timeout 1200 ./tri_d 256 3000 12 0 > runs/pinch0_N256.txt || true
python3 pool.py runs/pinch1_N512.txt runs/pinch0_N256.txt > results.txt
