#!/bin/bash
# usage: gowarm.sh ENTRY RP ROUND NROUNDS -- continue a vchain4 chain from round ROUND's unpruned dump with a warm
# Wentges centre (that dump's master dual); later rounds reload the columns with reduced cost <= RCEPS (rcprune.py)
cd "$(dirname "$0")"
e=$1; rp=$2; r=$3; n=${4:-4}
P=$(python3 -c "import json;print(json.dumps(json.load(open('entries.json'))['$e']))")
TL=${TL:-700} CG_ALPHA=${A:-0.3} WARM=1 RCEPS=${RCEPS:-0.4} CG_CENTER=v2_${rp}_${e}_$r.json PREV=v2_${rp}_${e}_$r.json K0=$((r+1)) \
  exec ./vchain4.sh $e "$P" 2 $rp $n
