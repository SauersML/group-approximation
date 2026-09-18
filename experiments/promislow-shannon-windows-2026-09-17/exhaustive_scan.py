#!/usr/bin/env python3
"""Exhaustive small-window census: E ranges over sets containing 1 inside a finite box B, |E| in SIZES;
F = R u N with R a set of at least two readers of the special site (R inside E^-1) and N at most NMAX
non-readers from B. Prints every configuration with ground set size at most MAXN.

usage: exhaustive_scan.py GROUP MAXN SIZES NMAX     GROUP in zz2 (box [-1,1] x Z/2), zz2w (box [-2,2] x Z/2)
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'shannon-window-certificates-2026-09-17'))
from shannon_lp import build, solve, show
from torsion2_scan import ZxZ2

name, maxn = sys.argv[1], int(sys.argv[2])
sizes = [int(v) for v in sys.argv[3].split(',')]
nmax = int(sys.argv[4])
if name == 'zz2':
    G = ZxZ2(); B = [(a, b) for a in (-1, 0, 1) for b in (0, 1)]
elif name == 'zz2w':
    G = ZxZ2(); B = [(a, b) for a in (-2, -1, 0, 1, 2) for b in (0, 1)]
others = [b for b in B if b != G.one]
seen = set()
cnt = 0; low = 0
for k in sizes:
    for rest in itertools.combinations(others, k - 1):
        E = [G.one] + list(rest)
        Einv = [G.inv(e) for e in E]
        for r in range(2, len(Einv) + 1):
            for R in itertools.combinations(Einv, r):
                nonr = [b for b in B if b not in Einv]
                for nn in range(0, nmax + 1):
                    for N in itertools.combinations(nonr, nn):
                        F = list(R) + list(N)
                        key = (tuple(sorted(E)), tuple(sorted(F)))
                        if key in seen:
                            continue
                        seen.add(key)
                        d = build(G, E, F)
                        if d['n'] > maxn:
                            continue
                        res, _ = solve(d)
                        cnt += 1
                        flag = '  <<< BELOW 1' if res.fun < 1 - 1e-6 else ''
                        low += bool(flag)
                        print('%s E=%s F=%s n=%d nv=%d LP=%.6f%s' % (name, show(G, E), show(G, F), d['n'], d['nv'], res.fun, flag), flush=True)
print('# total %d configurations, %d below 1' % (cnt, low))
