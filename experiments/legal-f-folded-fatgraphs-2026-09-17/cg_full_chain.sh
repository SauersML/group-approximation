#!/bin/bash
# cg_full_chain.sh ID PHI NRUNS : chained cg_full.py runs on the full memory-2 LP at power 2, each under 1200 s;
# run i reloads the columns of run i-1 (pruned by reduced cost, CG_RCKEEP)
id=$1; phi=$2; n=$3
export CG_RHO_EVERY=4 CG_SIGN=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
log=cg_full_r2_${id}_m2_chain.log
if [ ! -f full_${id}_0.json ]; then
  nice -n 10 timeout 1200 python3 cg_full.py "$phi" 2 2 --prune-seed ${SEEDOPT} --cache prop_${id}.npz --kcol 6000 --tl 1120 --dual full_${id}_0.json >> $log 2>&1
fi
if [ ! -f full_${id}_0.json ] && [ -f full_${id}_0.json.seed.json ]; then
  echo "=== run 0 from pruned seed" >> $log
  nice -n 10 timeout 1200 python3 cg_full.py "$phi" 2 2 --cache prop_${id}.npz --load full_${id}_0.json.seed.json --kcol 6000 --tl ${TLRUN:-900} --dual full_${id}_0.json >> $log 2>&1
fi
for i in $(seq 1 $n); do
  p=$((i-1)); [ -f full_${id}_$p.json ] || break
  echo "=== run $i" >> $log
  nice -n 10 timeout 1200 python3 cg_full.py "$phi" 2 2 --cache prop_${id}.npz --load full_${id}_$p.json --kcol 6000 --tl ${TLRUN:-900} --dual full_${id}_$i.json >> $log 2>&1
  grep -q "RESULT infeasible\|RESULT ('negative'\|optimum >= 0" <(tail -3 $log) && break
  [ -f full_${id}_$i.json ] && rm -f full_${id}_$((p-1)).json
done
echo CHAIN DONE >> $log
