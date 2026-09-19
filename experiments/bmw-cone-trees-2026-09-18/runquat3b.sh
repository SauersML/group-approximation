#!/bin/bash
# strict char-3 search in D = (-1, t+1) over F_3(t), V = t, H = t-1, on the remaining (4,4) classes that
# FAIL the local-action filter (the filter is heuristic; this tests whether it loses models)
cd $(dirname $0)
for pat in 40_40 41_40 41_41 42_40 42_41 42_42; do
  cls=$(python3 -c "
import json; d=json.load(open('localfilter.json')); R=json.load(open('remaining.json'))
print(' '.join(str(c) for c in R['$pat'] if not d['$pat#%d'%c]['pass_']))")
  [ -z "$cls" ] && continue
  STRICT=1 nice -n 10 timeout 1200 python3 findquat3.py census_$pat.json 2 11 01 21 1 $cls
done
