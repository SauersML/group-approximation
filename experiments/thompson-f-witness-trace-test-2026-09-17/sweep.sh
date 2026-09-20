#!/bin/sh
# Fair comparison of the single-separation census (L=4, S={c}) with multi-separation (L=6: 3 classes,
# L=8: 17 classes), identical optimizer, tau=1.8.  Random restarts at n=4,8,16; then warm-start
# doubling (block copies + noise, as in the w19 census) to n=32 from the n=16 witness of the same L.
cd "$(dirname "$0")"
for L in 4 6 8; do
  for n in 4 8 16; do
    python3 constrained_census.py --n $n --L $L --restarts 3 --steps 1500 --save wit_L${L}_n${n}.npy
  done
  python3 constrained_census.py --n 32 --L $L --restarts 1 --steps 1000 --init wit_L${L}_n16.npy --noise 0.05 --save wit_L${L}_n32.npy
done
