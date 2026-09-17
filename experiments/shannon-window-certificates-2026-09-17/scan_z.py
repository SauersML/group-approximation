#!/usr/bin/env python3
"""Scan Z configurations: E = {0, e1, e2} within [0, 3], F within [-4, 4], |F| = 2 or 3, F meeting -E.
Translating F changes the configuration only by a shift of the special site, so F is not normalised."""
import itertools, sys
from shannon_lp import Zd, build, solve, show

G = Zd(1)
maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 12
for E in itertools.combinations(range(1, 4), 2):
    E = [(0,)] + [(e,) for e in E]
    for s in (2, 3):
        for F in itertools.combinations(range(-4, 5), s):
            if not (set(F) & set(-e[0] for e in E)):
                continue
            Ft = [(f,) for f in F]
            d = build(G, E, Ft)
            if d['n'] > maxn:
                continue
            res, _ = solve(d)
            print('E=%s F=%s n=%d LP=%.6f' % (show(G, E), show(G, Ft), d['n'], res.fun), flush=True)
