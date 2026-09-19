#!/bin/bash
# usage: vchain2.sh NAME 'PHI0' rm rp nrounds  -- chained mixed-memory CG runs (column checkpoints); after each
# round, the exact Farkas check of farkas_vmem.py on the final dual; stop at the first verified certificate
name=$1; P=$2; rm_=$3; rp_=$4; n=$5
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 CG_RHO_EVERY=${CG_RHO_EVERY:-4}
tag=v${rm_}_${rp_}_$name
prev=""
for k in $(seq 0 $((n-1))); do
  ld=""; [ -n "$prev" ] && ld="--load $prev"
  nice -n 10 timeout 1200 python3 vcg.py "$P" 2 $rm_ $rp_ --kcol 3000 --tl 1080 --dual ${tag}_$k.json $ld > ${tag}_$k.log 2>&1
  [ -s ${tag}_$k.json ] && prev=${tag}_$k.json
  if [ -s ${tag}_$k.json ]; then
    nice -n 10 timeout 1200 python3 farkas_vmem.py ${tag}_$k.json --key y --save farkas_vmem_m2_${name}_rm${rm_}_rp${rp_}.json > farkas_${tag}_$k.log 2>&1
    grep -q "FARKAS VERIFIED" farkas_${tag}_$k.log && { echo "VERIFIED round $k"; break; }
  fi
  grep -q "^RESULT" ${tag}_$k.log && ! grep -q "^RESULT ('timeout'" ${tag}_$k.log && ! grep -q "^RESULT infeasible" ${tag}_$k.log && { echo "STOP $(grep ^RESULT ${tag}_$k.log)"; break; }
done
echo CHAIN DONE
