#!/usr/bin/env python3
"""Scan small free-group configurations: E subset of the unit ball containing 1, |E| = 3,
F subset of the radius-2 ball, |F| = 2 or 3, F meeting E^-1. Print the Shannon LP value of Phi."""
import itertools, sys
from shannon_lp import Free, build, solve, show

G = Free
B1 = ['', 'a', 'A', 'b', 'B']
B2 = sorted(set(G.mul(u, v) for u in B1 for v in B1), key=lambda w: (len(w), w))
maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 12
sizes = [int(s) for s in sys.argv[2].split(',')] if len(sys.argv) > 2 else [2, 3]
seen = set()
def canon(E, F):
    # images under the 8 signed permutations of generators
    best = None
    for swap in (False, True):
        for sa in (False, True):
            for sb in (False, True):
                mp = {}
                A1, B1_ = ('b', 'a') if swap else ('a', 'b')
                if sa: A1 = G.inv(A1)
                if sb: B1_ = G.inv(B1_)
                mp = {'a': A1, 'A': G.inv(A1), 'b': B1_, 'B': G.inv(B1_)}
                f = lambda w: ''.join(mp[c] for c in w)
                key = (tuple(sorted(f(e) for e in E)), tuple(sorted(f(x) for x in F)))
                best = key if best is None or key < best else best
    return best
for E in itertools.combinations(B1[1:], 2):
    E = [''] + list(E)
    Einv = set(G.inv(e) for e in E)
    for s in sizes:
        for F in itertools.combinations(B2, s):
            if not (set(F) & Einv):
                continue
            key = canon(E, F)
            if key in seen:
                continue
            seen.add(key)
            d = build(G, E, list(F))
            if d['n'] > maxn:
                continue
            res, _ = solve(d)
            print('E=%s F=%s n=%d LP=%.6f' % (show(G, E), show(G, F), d['n'], res.fun), flush=True)
