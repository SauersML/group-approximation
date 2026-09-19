#!/bin/sh
# Pass 1 of the conjugate-frame search over the transposed-letter candidates without a chain in
# ../bmw-klein-chains-transposed-2026-09-17/chains_X.json.  Args: L S NB CAP tag [extra flags]
# (CHK: directory holding out_X.jsonl and the previous lane's chains_X.json; C: census directory)
L=$1; S=$2; NB=$3; CAP=$4; TAG=$5; shift 5
C=${C:-/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17}
for rep in 1 2 3; do for p in 41_30 41_31 42_30 42_31 42_42 52_31 52_30 50_31 51_31 42_41 42_40 41_41 51_30 41_40; do
  SKIP=$CHK/chains_$p.json
  [ -f chains_$p.json ] && python3 -c "import json;a=json.load(open('$SKIP'));a.update(json.load(open('chains_$p.json')));json.dump(a,open('/tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/skip_$p.json','w'))" && SKIP=/tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/skip_$p.json
  nice -n 10 timeout 1200 python3 kframe.py $C/census_$p.json cand $L $S $NB --cand $CHK/out_$p.jsonl \
    --skip $SKIP --cap $CAP --out chains_$p.json --log kf_${TAG}_$p.jsonl "$@" > /dev/null
done; done
