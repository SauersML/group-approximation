#!/bin/bash
# Kernel profiles k = 0..7 (window N = k+3) for the sampled solved and stubborn P_(2,2) pairs, plus
# S_(2,4) calibration through k = 7.  Writes prof_small.jsonl; ends with DONE.
set -u
cd "$(dirname "$0")"
SOLVED=$(/usr/bin/python3.12 -c "
import json; d=json.load(open('samples.json')); print(' '.join(f\"{p['a']} {p['b']}\" for p in d['solved']))")
STUB=$(/usr/bin/python3.12 -c "
import json; d=json.load(open('samples.json')); print(' '.join(f\"{p['a']} {p['b']}\" for p in d['stubborn']))")
S24=$(/usr/bin/python3.12 -c "
import json; d=json.load(open('samples.json')); print(' '.join(f\"{p['a']} {p['b']}\" for p in d['s24']))")
: > prof_small.jsonl
for k in 0 1 2 3 4 5 6 7; do
  ./kprof S35 $k 3 ore $SOLVED $STUB >> prof_small.jsonl
  ./kprof S24 $k 3 ore $S24 >> prof_small.jsonl
done
echo DONE
