#!/bin/sh
# Warm-started F searches: n = 32 and 48 seeded by block copies of the certified n = 16 witness.
cd "$(dirname "$0")"
for spec in "32 0.05" "32 0.15" "48 0.05" "48 0.15"; do echo "$spec"; done |
  xargs -P 4 -n 2 sh -c 'python3 defect_profile.py --group F --n "$0" --tau 1.8 --restarts 2 --steps 2000 --lr 0.01 --noise "$1" --init wit_F_n16_tau1.8.npy --save "wit_F_n$0_warm_noise$1.npy"' > warm_runs.out
