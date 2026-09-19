#!/bin/sh
# Warm-start doubling, next rung: n = 128 seeded by block copies of the n = 64 witness.
cd "$(dirname "$0")"
for spec in "0.05 21" "0.10 22"; do echo "$spec"; done |
  xargs -P 2 -n 2 sh -c 'python3 defect_profile.py --group F --n 128 --tau 1.8 --restarts 1 --steps 1000 --lr 0.01 --noise "$0" --seed "$1" --init wit_F_n64_warm_noise0.08.npy --save "wit_F_n128_warm_noise$0.npy"' > warm_runs128.out
