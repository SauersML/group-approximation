#!/bin/sh
# Run kpure2.py --powers at L = 6 on every census candidate (automaton image not certified finite) of each
# given pattern.
C=../bmw-census-left-orders-2026-09-17
for p in "$@"; do
  nice -n 10 timeout 1200 python3 kpure2.py $C/census_$p.json 6 kpp2_${p}_L6.jsonl cand --cand $C/out_$p.jsonl --powers > /dev/null
done
