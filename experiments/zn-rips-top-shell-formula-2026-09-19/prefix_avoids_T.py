#!/usr/bin/env python3
"""prefix_avoids_T.py [DIR]: check that no (D) line of the (8,11) prefix or tail uses a point of T.

DIR defaults to experiments/zn-rips-link-collapse-scale-11-2026-09-19 (node
z8-rips-scale-11-reduces-to-top-shell-link-collapses).  Reads sets/T-8-11.txt.gz (one point per line) and
certs/d-prefix-8-11.txt.gz, certs/d-tail-8-11.txt.gz (lines "A x1..x8 | w1..w8" or "D x1..x8 | w1..w8",
the vcert2 format).  For each file prints the line count, the count per tag, and how many lines have x in T
or w in T.  Monotonicity (proof section 7) needs both counts to be 0.
"""
import gzip, sys, collections
d = sys.argv[1] if len(sys.argv) > 1 else 'experiments/zn-rips-link-collapse-scale-11-2026-09-19'
T = set()
with gzip.open(d + '/sets/T-8-11.txt.gz', 'rt') as f:
    for line in f:
        p = tuple(map(int, line.split()))
        if p: T.add(p)
print('|T| =', len(T))
for name in ('d-prefix-8-11', 'd-tail-8-11'):
    tags = collections.Counter(); xin = win = n = 0
    with gzip.open(d + '/certs/' + name + '.txt.gz', 'rt') as f:
        for line in f:
            s = line.split()
            if not s: continue
            n += 1; tags[s[0]] += 1
            k = s.index('|')
            x = tuple(map(int, s[1:k])); w = tuple(map(int, s[k + 1:]))
            assert len(x) == 8 and len(w) == 8, line
            xin += x in T; win += w in T
    print(name, 'lines', n, dict(tags), 'x in T', xin, 'w in T', win)
