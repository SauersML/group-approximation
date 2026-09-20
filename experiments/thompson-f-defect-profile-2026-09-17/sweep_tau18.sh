#!/bin/sh
# Large-separation sweep: D_n(1.8) upper bounds for F, BG, H4 at n = 4, 8, 16.
# At tau = 1.8 direct-sum mixing with trivial blocks cannot lower the defect below
# (tau - 2 + 2/k)-type thresholds, so this regime is the informative one.
cd "$(dirname "$0")"
for n in 4 8 16; do
  for g in F BG H4; do
    echo "$g $n"
  done
done | xargs -P 3 -n 2 sh -c 'python3 defect_profile.py --group "$0" --n "$1" --tau 1.8 --restarts 4 --steps 1500' > sweep_tau18.out
