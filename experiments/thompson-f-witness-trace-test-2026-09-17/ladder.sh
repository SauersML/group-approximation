#!/bin/sh
# Warm-start doubling ladder (the w19 protocol) for the census with S = F' classes of length <= L.
# Each rung starts from block copies of the best previous witness plus noise.  By monotonicity
# (direct sums preserve all e-values) the true D_n is at most the running minimum.
# Usage: sh ladder.sh L   (identical protocol for L=4, i.e. S={c}, and L=8, 17 classes)
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1
L=$1
prev=wit_L${L}_n8.npy
for n in 16 32 64; do
  python3 constrained_census.py --n $n --L $L --restarts 1 --steps 1500 --init $prev --noise 0.03 --save wit_L${L}_n${n}_warm.npy
  prev=wit_L${L}_n${n}_warm.npy
done
