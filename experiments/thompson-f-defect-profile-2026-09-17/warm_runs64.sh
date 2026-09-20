#!/bin/sh
# Warm-start doubling, next rung: n = 64 seeded by block copies of the certified n = 32 witness.
cd "$(dirname "$0")"
for spec in "0.03 11" "0.08 12"; do echo "$spec"; done |
  xargs -P 2 -n 2 sh -c 'python3 defect_profile.py --group F --n 64 --tau 1.8 --restarts 1 --steps 1500 --lr 0.01 --noise "$0" --seed "$1" --init wit_F_n32_warm_noise0.05.npy --save "wit_F_n64_warm_noise$0.npy"' > warm_runs64.out
