#!/usr/bin/env python3
"""Tietze-closure tests on the primary-census survivors.
usage: survivorsp4.py '<glob of *_survivors.jsonl>' out.jsonl"""
import json, sys, glob, collections
from lot4 import tietze_closure_test
tally, hard = collections.Counter(), []
with open(sys.argv[2], 'w') as fh:
    for f in sorted(glob.glob(sys.argv[1])):
        for line in open(f):
            E = [tuple(e) for e in json.loads(line)]; n = len(E) + 1
            name, cert = tietze_closure_test(n, E)
            fh.write(json.dumps({'file': f.split('/')[-1], 'lot': E, 'tietze': name, 'cert': cert}) + '\n')
            tally[str(name)] += 1
            print('LOT', E, '->', name, json.dumps(cert)[:160], flush=True)
            if name is None: hard.append(E)
print('SURVIVORSP4', dict(tally), 'hard', len(hard), flush=True)
