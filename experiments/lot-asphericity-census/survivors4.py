#!/usr/bin/env python3
"""Tietze-closure tests (lot4.py) on classes that survive the relative test.
usage: survivors4.py survivors3.jsonl out.jsonl"""
import json, sys, collections
from lot4 import tietze_closure_test
tally, hard = collections.Counter(), []
with open(sys.argv[2], 'w') as fh:
    for line in open(sys.argv[1]):
        r = json.loads(line)
        if r.get('relative_primary'): continue
        E = [tuple(e) for e in r['lot']]
        name, cert = tietze_closure_test(r['n'], E)
        fh.write(json.dumps(dict(r, tietze=name, tietze_cert=cert)) + '\n')
        tally[str(name)] += 1
        print('LOT', r['lot'], '->', name, json.dumps(cert)[:200], flush=True)
        if name is None: hard.append(r['lot'])
print('SURVIVORS4', dict(tally), 'hard', len(hard), flush=True)
