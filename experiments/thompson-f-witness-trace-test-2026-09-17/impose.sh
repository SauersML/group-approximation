#!/bin/sh
# Start from the certified w19 single-separation witnesses and re-optimize under the 17-class
# constraint (L=8), same dimension, small noise: what does F-trace consistency cost the best known
# configurations?  Control: the same re-optimization with L=4 (S={c}) from the same start.
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1
for w in 16 32 64b; do
  n=$(echo $w | tr -d b)
  for L in 4 8; do
    python3 constrained_census.py --n $n --L $L --restarts 1 --steps 1500 --lr 0.01 --init wit_F_n${w}.npy --noise 0.01 --save wit_impose_L${L}_n${w}.npy
  done
done
