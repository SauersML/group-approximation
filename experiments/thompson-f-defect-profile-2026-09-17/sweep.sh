#!/bin/sh
# Defect-profile sweep: D_n(1.0) upper bounds for F, BG, H4 at n = 2..32 (4 parallel jobs).
cd "$(dirname "$0")"
for n in 2 4 8 16 32; do
  for g in F BG H4; do
    echo "$g $n"
  done
done | xargs -P 4 -n 2 sh -c 'python3 defect_profile.py --group "$0" --n "$1" --tau 1.0 --restarts 4 --steps 1500' > sweep.out
