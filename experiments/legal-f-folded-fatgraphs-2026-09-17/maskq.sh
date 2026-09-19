#!/bin/bash
# masked mixed-memory LP (VCG_MASK) diagnostics: usage maskq.sh RP entry:mask ...
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
rp=$1; shift
for em in "$@"; do
  e=${em%%:*}; mk=${em##*:}
  P=$(python3 -c "import json;print(json.dumps(json.load(open('entries.json'))['$e']))")
  VCG_MASK=$mk nice -n 10 timeout 1200 python3 vcg.py "$P" 2 2 $rp --kcol 2000 --tl 900 > vcgmask_${e}_${mk}_$rp.log 2>&1
  echo "$e $mk $rp $(grep -E '^phase' vcgmask_${e}_${mk}_$rp.log | tail -n 1 | cut -c1-60) $(grep '^RESULT' vcgmask_${e}_${mk}_$rp.log)"
done
