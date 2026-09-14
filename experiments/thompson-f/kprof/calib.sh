#!/bin/bash
# Calibration of kprof.c on MSI (small degrees): cross-check against kprof_check.py, free-monoid
# control, and known minimal degrees for S_(2,4).  Writes calib.out; ends with DONE.
set -u
cd "$(dirname "$0")"
gcc -O2 -march=native -o kprof kprof.c 2>&1 | tail -5
md5sum kprof.c kprof_check.py sample_pairs.py > md5.txt
/usr/bin/python3.12 sample_pairs.py
echo "== cross-check S35 k<=5 (C vs Python), pairs: 2 solved + 2 stubborn + (1,2)"
PAIRS=$(/usr/bin/python3.12 -c "
import json; d=json.load(open('samples.json'))
ps=[(1,2)]+[(p['a'],p['b']) for p in d['solved'][:2]]+[(p['a'],p['b']) for p in d['stubborn'][:2]]
print(' '.join(f'{a} {b}' for a,b in ps))")
for k in 0 1 2 3 4 5; do ./kprof S35 $k 3 ore $PAIRS; done > c_s35.jsonl
/usr/bin/python3.12 kprof_check.py S35 5 3 ore $PAIRS > py_s35.jsonl
echo "== cross-check S24 k<=5"
S24=$(/usr/bin/python3.12 -c "
import json; d=json.load(open('samples.json')); print(' '.join(f\"{p['a']} {p['b']}\" for p in d['s24']))")
for k in 0 1 2 3 4 5; do ./kprof S24 $k 3 ore $S24; done > c_s24.jsonl
/usr/bin/python3.12 kprof_check.py S24 5 3 ore $S24 > py_s24.jsonl
echo "== free control S35 k<=4 (C and Python)"
FREE="1 16 3 16 7 56 1 2"
for k in 0 1 2 3 4; do ./kprof S35 $k 1 free $FREE; done > c_free.jsonl
/usr/bin/python3.12 kprof_check.py S35 4 1 free $FREE > py_free.jsonl
/usr/bin/python3.12 - <<'EOF'
import json
def load(f):
    out={}
    for line in open(f):
        d=json.loads(line); out[(d['k'],d['a'],d['b'])]=(d['V'],d['rows'],d['rank'],d['kernel'])
    return out
ok=True
for c,p in [('c_s35.jsonl','py_s35.jsonl'),('c_s24.jsonl','py_s24.jsonl'),('c_free.jsonl','py_free.jsonl')]:
    C=load(c); P=load(p)
    same = C==P
    ok &= same
    print(c, p, 'MATCH' if same else 'MISMATCH', len(C), len(P))
    if not same:
        for key in sorted(set(C)|set(P)):
            if C.get(key)!=P.get(key): print(' ', key, C.get(key), P.get(key))
free=load('c_free.jsonl')
print('free kernels', sorted(set(v[3] for v in free.values())))
print('CALIB_OK' if ok and all(v[3]==0 for v in free.values()) else 'CALIB_FAIL')
EOF
echo DONE
