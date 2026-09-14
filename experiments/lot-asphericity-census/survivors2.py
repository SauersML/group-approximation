#!/usr/bin/env python3
"""Run the second-tier tests of lot2.py on census survivors.
usage: survivors2.py '<glob of *_survivors.jsonl>' out.jsonl"""
import json, glob, sys, collections
from lot2 import certify2
from lot import cyclomatic, diameter

files = sorted(glob.glob(sys.argv[1]))
tally, hard = collections.Counter(), []
with open(sys.argv[2], 'w') as fh:
    for f in files:
        for line in open(f):
            E = [tuple(e) for e in json.loads(line)]; n = len(E) + 1
            name, cert = certify2(n, E)
            rec = {'file': f.split('/')[-1], 'n': n, 'lot': E, 'diam': diameter(n, E),
                   'labels': len({l for _, l, _ in E}),
                   'I_cyc': cyclomatic(n, [(l, t) for i, l, t in E]),
                   'T_cyc': cyclomatic(n, [(l, i) for i, l, t in E]), 'test': name, 'cert': cert}
            fh.write(json.dumps(rec) + '\n'); tally[str(name)] += 1
            if name is None: hard.append(rec)
print('SURVIVORS2', dict(tally), 'hard', len(hard))
for r in hard[:40]:
    print('HARD', r['file'], 'labels', r['labels'], 'I', r['I_cyc'], 'T', r['T_cyc'], 'diam', r['diam'], r['lot'])
