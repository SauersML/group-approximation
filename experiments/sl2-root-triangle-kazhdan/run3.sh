#!/bin/bash
# run3.sh -- model test of the untwisted member (GAP), then the first-level p = 2 moment test for q = 4 (calibration
# against GAP's H_1 of the kernel) and q = 8 (the Kazhdan case).
cd /scratch.global/sauer354/ex/ex2-triangle-persistence || exit 1
module load sagemath/10.7 2>/dev/null
export OMP_NUM_THREADS=8 OPENBLAS_NUM_THREADS=8 MKL_NUM_THREADS=8
echo "=== untw.g"
timeout 1500 sage -gap -q untw.g 2>&1
for spec in "4 2 1" "6 3 1"; do
  echo "=== moment2 $spec"
  timeout 3000 sage -python moment2.py $spec 2>&1
done
echo ALLDONE
