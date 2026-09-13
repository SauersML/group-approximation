#!/bin/bash
# run4.sh -- first-level p = 2 moment test for the untwisted member: q = 4 (calibration: GAP gives
# H_1(ker;Z) = 2^11 4^9, so b_1(N;F_2) = 20) and q = 8 (the Kazhdan case).
cd /scratch.global/sauer354/ex/ex2-triangle-persistence || exit 1
module load sagemath/10.7 2>/dev/null
export OMP_NUM_THREADS=8 OPENBLAS_NUM_THREADS=8 MKL_NUM_THREADS=8
for spec in "4 2 1" "6 3 1"; do
  echo "=== moment2 $spec"
  timeout 3000 sage -python moment2.py $spec 2>&1
done
echo ALLDONE
