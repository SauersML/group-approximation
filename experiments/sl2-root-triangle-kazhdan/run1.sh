#!/bin/bash
# run1.sh -- calibration (root links of SL_2(8), SL_2(16)) and the subfield links of SL_2(16), SL_2(64), SL_2(256)
cd /scratch.global/sauer354/ex/ex2-triangle-persistence || exit 1
module load sagemath/10.7 2>/dev/null
export OMP_NUM_THREADS=8 OPENBLAS_NUM_THREADS=8 MKL_NUM_THREADS=8
for spec in "3 3 -1 20" "4 4 -1 20" "4 2 1 60 1 2" "6 3 1 400 3 4" "8 4 1 60 7 8"; do
  set -- $spec
  echo "=== n=$1 f=$2 s_exp=$3 mmax=$4 theta=$5/$6"
  timeout 3000 sage -python sl2link.py $spec 2>&1
done
echo ALLDONE
