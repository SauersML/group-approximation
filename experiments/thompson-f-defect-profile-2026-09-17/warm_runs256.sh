#!/bin/sh
# Warm-start doubling, next rung: n = 256 seeded by block copies of the n = 128 witness.
cd "$(dirname "$0")"
for spec in "0.03 31" "0.05 32"; do echo "$spec"; done |
  xargs -P 2 -n 2 sh -c 'python3 defect_profile.py --group F --n 256 --tau 1.8 --restarts 1 --steps 800 --lr 0.01 --noise "$0" --seed "$1" --init wit_F_n128_warm_noise0.05.npy --save "wit_F_n256_warm_noise$0.npy"' > warm_runs256.out
