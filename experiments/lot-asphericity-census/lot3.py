#!/usr/bin/env python3
"""Relative test for LOT complexes (Harlander--Rosebrock, arXiv:1912.12512v2).

Theorem 3.4: let K = K_1 v ... v K_n <= L, where the 2-cells of L have exponent sum 0 and the K_i
are full.  If lk+(L) is a forest relative to lk+(K), or lk-(L) is a forest relative to lk-(K),
then L is VA relative to K.  Theorem 2.4: if L is VA relative to K and K is aspherical, then L is
aspherical.  For a LOT, K_i = K(Gamma_i) for vertex-disjoint sub-LOTs, lk+ and lk- are the graphs
I(Gamma) and T(Gamma), and Definition 3.2 collapses each lk+-(K_i) to a point.  A wedge of
aspherical 2-complexes is aspherical.
"""
import itertools
from lot import certify
from lot2 import certify2

def sub_lots(n, E):
    """Proper sub-LOTs: connected edge sets whose labels lie in their own vertex set."""
    m, out = len(E), []
    for mask in range(1, (1 << m) - 1):
        S = [E[k] for k in range(m) if mask >> k & 1]
        V = {x for (i, l, t) in S for x in (i, t)}
        if len(V) == len(S) + 1 and all(l in V for (_, l, _) in S):
            out.append((mask, frozenset(V), S))
    return out

def rel_forest(n, E, fam, Kmask, side):
    p = list(range(n))
    def f(x):
        while p[x] != x: p[x] = p[p[x]]; x = p[x]
        return x
    for s in fam:
        vs = sorted(s[1])
        for v in vs[1:]: p[f(v)] = f(vs[0])
    for k, (i, l, t) in enumerate(E):
        if Kmask >> k & 1: continue
        u, v = (l, t) if side == 'I' else (l, i)
        if f(u) == f(v): return False
        p[f(u)] = f(v)
    return True

def certify_any(n, E, depth=0):
    """First tier (lot.py), second tier (lot2.py), then the relative test, on the reduction."""
    red, name, cert = certify(n, E)
    if name: return name, cert
    rn, rE = red
    name, cert = certify2(rn, rE)
    if name: return name, cert
    if depth < 3:
        c = test_relative(rn, rE, depth)
        if c: return 'relative', c
    return None, None

def test_relative(n, E, depth=0, max_family=3):
    subs, cache = sub_lots(n, E), {}
    def sub_ok(s):
        if s[0] not in cache:
            idx = {v: r for r, v in enumerate(sorted(s[1]))}
            SE = [tuple(idx[x] for x in e) for e in s[2]]
            cache[s[0]] = certify_any(len(s[1]), SE, depth + 1)[0]
        return cache[s[0]]
    for size in range(1, max_family + 1):
        for fam in itertools.combinations(subs, size):
            Vs = [s[1] for s in fam]
            if any(a & b for a, b in itertools.combinations(Vs, 2)): continue
            Vall, Kmask = set().union(*Vs), 0
            for s in fam: Kmask |= s[0]
            if any(not (Kmask >> k & 1) and {i, l, t} <= Vall for k, (i, l, t) in enumerate(E)):
                continue                                   # K not full
            for side in ('I', 'T'):
                if rel_forest(n, E, fam, Kmask, side) and all(sub_ok(s) for s in fam):
                    return {'side': side, 'subs': [s[2] for s in fam],
                            'sub_tests': [cache[s[0]] for s in fam]}
    return None
