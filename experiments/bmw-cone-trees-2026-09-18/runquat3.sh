#!/bin/bash
# strict char-3 quaternion search on the (4,4) classes passing the local-action filter
cd $(dirname $0)
for pat in 40_40 41_40 41_41 42_40 42_41 42_42; do
  cls=$(python3 -c "
import json; d=json.load(open('localfilter.json')); print(' '.join(k.split('#')[1] for k,v in d.items() if k.split('#')[0]=='$pat' and v['pass_']))")
  [ -z "$cls" ] && continue
  for alg in "2 11 1" "11 122 2" "11 202 2"; do
    set -- $alg
    STRICT=1 nice -n 10 timeout 3000 python3 findquat3.py census_$pat.json $1 $2 01 21 $3 $cls
  done
done
