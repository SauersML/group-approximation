#!/usr/bin/env python3
"""Count bs_search.py OPEN lines (stdin) up to the census symmetries (height reversal, inversion,
a -> a^-1, cyclic rotation), by (p, q) and relator length.  Usage: canon_counts.py N < file"""
import sys
from ast import literal_eval
from collections import Counter
N = int(sys.argv[1])
def canon(seq):
    best = None; k = len(seq)
    for s in (seq, [(N - h, e) for h, e in seq]):
        for v in (s, [(h, -e) for h, e in reversed(s)]):
            for sg in (1, -1):
                vv = [(h, sg * e) for h, e in v]
                for r in range(k):
                    u = tuple(vv[r:] + vv[:r])
                    if best is None or u < best: best = u
    return best
d = {}
for l in sys.stdin:
    f = l.split()
    if f and f[0] == 'OPEN':
        d.setdefault((int(f[3]), int(f[4])), {}).setdefault(canon(literal_eval(f[8])), int(f[2]))
for k, v in sorted(d.items()):
    print('BS%s: %d classes; by length %s' % (k, len(v), sorted(Counter(v.values()).items())))
