#!/usr/bin/env python3
"""Relative test (Harlander--Rosebrock Thms 3.4 and 2.4) on second-tier survivors.
usage: survivors3.py survivors2.jsonl out.jsonl"""
import json, sys, collections
from lot3 import test_relative
from lot_primary import relative_primary
tally, hard = collections.Counter(), []
with open(sys.argv[2], 'w') as fh:
    for line in open(sys.argv[1]):
        r = json.loads(line)
        if r['test'] is not None: continue
        E = [tuple(e) for e in r['lot']]; n = r['n']
        c, cp = test_relative(n, E), relative_primary(n, E)
        fh.write(json.dumps(dict(r, relative=c, relative_primary=cp)) + '\n')
        tally['relative' if c else 'rel_none'] += 1; tally['primary' if cp else 'prim_none'] += 1
        if not cp: hard.append(r['lot'])
print('SURVIVORS3', dict(tally), flush=True)
for h in hard: print('HARD3', h)
