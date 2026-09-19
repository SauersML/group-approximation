#!/usr/bin/env python3
"""Level-1 stabilizer calculus for the loop subgroup H = <s,t,u> (chain (a,a,e) survivor)."""
import sys as _sys, os as _os
_HERE = _os.path.dirname(_os.path.abspath(__file__))
for _d in ('loop-graph-screen-2026-09-18', 'poly-star-obstruction-2026-09-19'):
    _sys.path.insert(0, _os.path.join(_HERE, '..', _d))
import itertools
from collections import deque
from poly_star_screen import family
from loopgraph import N, ID, W, reduce, inv, fmt, pmul, pinv

R = family("chain", "a", "a", "e", "", "", "")
HL = [("s", 1), ("t", 1), ("u", 1), ("s", -1), ("t", -1), ("u", -1)]

_triv = {}
def triv(w):
    w = reduce(w)
    if not w: return True
    if w not in _triv: _triv[w] = R.trivial(w)
    return _triv[w]

def secs(w): return [R.sec(w, x) for x in range(N)]
def supp(w): return frozenset(x for x, u in enumerate(secs(w)) if not triv(u))
def comm(x, y): return reduce(inv(x) + inv(y) + x + y)
def conj(x, h): return reduce(inv(h) + x + h)

def root_words(maxn=7920):
    """shortest H-word for each root permutation (BFS in M_11)"""
    best = {ID: ()}; q = deque([ID])
    while q and len(best) < maxn:
        p = q.popleft()
        for l in HL:
            r = pmul(p, R.lperm(*l))
            if r not in best: best[r] = best[p] + (l,); q.append(r)
    return best

def act_set(S, p): return frozenset(p[x] for x in S)
