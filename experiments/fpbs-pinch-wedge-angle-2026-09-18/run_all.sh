#!/bin/bash
# Reproduce results.txt. tri_wedge N samples seed pinch theta_deg [onesided]
# Output per sample: "Dmask Pmask", bit b <-> n = 8*2^b (D'_n(X_theta), 0 in I_n).
# Each run was capped at 1100 s wall time, so sample counts are below 6000.
set -e; cd "$(dirname "$0")"; gcc -O2 -o tri_wedge tri_wedge.c -lm; mkdir -p runs
for th in 0 90; do timeout 1100 ./tri_wedge 256 6000 $((20+th)) 1 $th > runs/th${th}_N256.txt || true; done
timeout 1100 ./tri_wedge 256 6000 77 1 90 1 > runs/half90_N256.txt || true   # quadrant X^+ = {x>0, y>=0}
python3 pool.py runs/th0_N256.txt runs/th90_N256.txt runs/half90_N256.txt > results.txt
