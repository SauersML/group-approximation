#!/bin/bash
# run2.sh -- the second Frobenius class of lines s*F_q (s = g^3) for q = 8, 16, and the symmetry check
# s = g^2 (same class as g, expected to reproduce run1 numbers).
cd /scratch.global/sauer354/ex/ex2-triangle-persistence || exit 1
module load sagemath/10.7 2>/dev/null
export OMP_NUM_THREADS=8 OPENBLAS_NUM_THREADS=8 MKL_NUM_THREADS=8
for spec in "6 3 2 120 3 4" "6 3 3 400 3 4" "8 4 3 60 7 8" "8 4 2 24 7 8"; do
  set -- $spec
  echo "=== n=$1 f=$2 s_exp=$3 mmax=$4 theta=$5/$6"
  timeout 3000 sage -python sl2link.py $spec 2>&1
done
echo ALLDONE
