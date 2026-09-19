#!/bin/bash
# Reproduce results.txt.  karm N samples seed [mode]; exh n (exhaustive, small n).
# mode 0 columns: A_UL A_LL A_UH A_LH D'(pi/2) D'(0) {0 in I_n}; mode 1 replaces the two D'
# columns by A_UR A_LR.  Bit b of each mask <-> n = 8*2^b.  Runs were capped at 1200 s wall
# time on a loaded machine, so sample counts are below the requested ones.
set -e; cd "$(dirname "$0")"; gcc -O2 -o karm karm.c; gcc -O2 -o exh exh.c; mkdir -p runs
timeout 1200 ./karm 256 8000 11 > runs/N256_s11.txt || true
timeout 1200 ./karm 512 3000 7 > runs/N512_s7.txt || true
timeout 1200 ./karm 256 20000 21 1 > runs/fast_N256_s21.txt || true
{ echo "# runs capped at 1200 s"; ./exh 2; ./exh 3
  echo "=== mode 0, n <= 256 (seed 11)"; python3 pool.py runs/N256_s11.txt
  echo "=== mode 0, n <= 512 (seed 7)"; python3 pool.py runs/N512_s7.txt
  echo "=== mode 1, n <= 256 (seed 21)"; python3 pool_fast.py runs/fast_N256_s21.txt
} > results.txt
