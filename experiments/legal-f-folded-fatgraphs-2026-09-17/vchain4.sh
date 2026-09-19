#!/bin/bash
# usage: [PREV=dump.json] [K0=k] vchain4.sh NAME 'PHI0' rm rp nrounds
# vchain2.sh (each checkpoint pruned by prune.py) with an optional starting column checkpoint (PREV) and first round index (K0): chained mixed-memory
# CG runs of vcg.py; after each round, the exact Farkas check of farkas_vmem.py; stop at the first verified certificate
name=$1; P=$2; rm_=$3; rp_=$4; n=$5
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 CG_RHO_EVERY=${CG_RHO_EVERY:-4}
tag=v${rm_}_${rp_}_$name
prev=${PREV:-}; k0=${K0:-0}
for k in $(seq $k0 $((k0+n-1))); do
  ld=""; [ -n "$prev" ] && ld="--load $prev"
  nice -n 10 timeout 1200 python3 vcg.py "$P" 2 $rm_ $rp_ --kcol 3000 --tl ${TL:-900} --dual ${tag}_$k.json $ld > ${tag}_$k.log 2>&1
  if [ -n "${RCEPS:-}" ]; then [ -s ${tag}_$k.json ] && python3 rcprune.py ${tag}_$k.json p_${tag}_$k.json $RCEPS > /dev/null && prev=p_${tag}_$k.json
  else [ -s ${tag}_$k.json ] && python3 prune.py ${tag}_$k.json p_${tag}_$k.json 1e-9 ${TAIL:-0} > /dev/null && prev=p_${tag}_$k.json; fi
  [ -s ${tag}_$k.json ] && [ -n "${WARM:-}" ] && export CG_CENTER=${tag}_$k.json
  if [ -s ${tag}_$k.json ]; then
    nice -n 10 timeout 1200 python3 farkas_vmem.py ${tag}_$k.json --key y --save farkas_vmem_m2_${name}_rm${rm_}_rp${rp_}.json > farkas_${tag}_$k.log 2>&1
    grep -q "FARKAS VERIFIED" farkas_${tag}_$k.log && { echo "$name VERIFIED round $k"; break; }
    if python3 -c "import json,sys; J=json.load(open('${tag}_$k.json')); sys.exit(0 if 'y_rho' in J else 1)"; then
      nice -n 10 timeout 1200 python3 farkas_vmem.py ${tag}_$k.json --key y_rho --save farkas_vmem_m2_${name}_rm${rm_}_rp${rp_}.json > farkas_rho_${tag}_$k.log 2>&1
      grep -q "FARKAS VERIFIED" farkas_rho_${tag}_$k.log && { echo "$name VERIFIED (y_rho) round $k"; break; }
    fi
  fi
  grep -q "^RESULT" ${tag}_$k.log && ! grep -q "^RESULT ('timeout'" ${tag}_$k.log && ! grep -q "^RESULT infeasible" ${tag}_$k.log && { echo "$name STOP $(grep ^RESULT ${tag}_$k.log)"; break; }
done
echo "$name CHAIN DONE"
