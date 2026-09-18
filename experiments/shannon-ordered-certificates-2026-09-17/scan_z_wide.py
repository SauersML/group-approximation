#!/usr/bin/env python3
"""Wider minimal-window census over Z: min E = 0, E in [0, emax], |E| in {3, 4}; F in [-fmax, fmax],
|F| in {2, 3, 4}, at least two readers of site 0 (|F cap -E| >= 2), ground set size n <= maxn.
Prints every configuration and flags LP < 1 - 1e-6.
usage: scan_z_wide.py emax fmax maxn"""
import itertools, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'shannon-window-certificates-2026-09-17'))
from shannon_lp import Zd, build, solve

emax, fmax, maxn = (int(a) for a in sys.argv[1:4])
G = Zd(1)
seen = set()
for s in (3, 4):
    for rest in itertools.combinations(range(1, emax + 1), s - 1):
        E = (0,) + rest
        for t in (2, 3, 4):
            for F in itertools.combinations(range(-fmax, fmax + 1), t):
                if len(set(F) & set(-e for e in E)) < 2:
                    continue
                key = (E, F)
                if key in seen:
                    continue
                seen.add(key)
                d = build(G, [(e,) for e in E], [(f,) for f in F])
                if d['n'] > maxn:
                    continue
                res, _ = solve(d)
                flag = '  FAKE?' if res.fun < 1 - 1e-6 else ''
                print('E=%s F=%s n=%d nv=%d LP=%.6f%s' % (E, F, d['n'], d['nv'], res.fun, flag), flush=True)
