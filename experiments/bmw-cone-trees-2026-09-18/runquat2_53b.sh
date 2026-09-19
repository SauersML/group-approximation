#!/bin/bash
# same search as runquat2_53.sh on the 58 even (A_5-compatible) (5,3) classes that fail the local-action filter
cd $(dirname $0)
for pc in $(python3 -c "
import json; P=json.load(open('parity5b.json')); L=json.load(open('localfilter.json'))
print(' '.join(k.replace('#',':') for k in sorted(P) if P[k]['even'] and not L[k]['pass_']))"); do
  p=${pc%:*}; c=${pc#*:}
  echo "== $p $c"
  nice -n 10 timeout 1200 python3 findquat.py census_$p.json $c 1 1 3 2 7
done
