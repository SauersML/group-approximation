#!/bin/sh
# Continue run_P6.sh for the given patterns: scan the candidates not yet in kpp2_X_L6.jsonl, in chunks of
# 20 classes per 1200 s run (each class's record is appended as soon as it is done).
C=../bmw-census-left-orders-2026-09-17
for p in "$@"; do
  touch kpp2_${p}_L6.jsonl
  python3 -c "
import json
done = {json.loads(l)['class'] for l in open('kpp2_${p}_L6.jsonl')}
c = [r['idx'] for r in map(json.loads, open('$C/out_${p}.jsonl')) if (r.get('finH') is None or r.get('finV') is None) and r['idx'] not in done]
for i in range(0, len(c), 20): print(','.join(map(str, c[i:i + 20])))
" | while read cls; do
    nice -n 10 timeout 1200 python3 kpure2.py $C/census_$p.json 6 kpp2_${p}_L6.jsonl $cls --powers > /dev/null
  done
done
