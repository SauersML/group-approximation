#!/bin/sh
# F witnesses at large separation, saved for exact certification (certify_ratio.py).
cd "$(dirname "$0")"
for spec in "16 1.8" "16 2.5" "32 1.8" "32 2.5"; do echo "$spec"; done |
  xargs -P 4 -n 2 sh -c 'python3 defect_profile.py --group F --n "$0" --tau "$1" --restarts 4 --steps 1500 --save "wit_F_n$0_tau$1.npy"' > witness_runs.out
