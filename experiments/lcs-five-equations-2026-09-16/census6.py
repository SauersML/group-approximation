#!/usr/bin/env python3
"""Informational census (2026-09-16): commutation closure vs planarity on 6 vertices.

For every labelled simple graph G on 6 vertices (2^15 graphs), run the
commutation-closure rule of verify.py on the generic-sign incidence group H(G)
(edges = involutions, adjacent edges commute, vertex products central).
Nonplanarity is decided by Kuratowski on 6 vertices: G is nonplanar iff it
contains K_{3,3}, K_5, or K_5 with one edge subdivided through the sixth vertex.

Output: the 2x2 table (closure complete?) x (planar?).  Complete closure makes
H(G) abelian, so it proves J=1 for any odd right-hand side; this census only
measures how much of Arkhipov's planar case the elementary rule reproduces.
It is not used in any proof.
"""
import itertools
from verify import closure

V = range(6)
PAIRS = list(itertools.combinations(V, 2))
IDX = {p: i for i, p in enumerate(PAIRS)}

def has(mask, u, v):
    return mask >> IDX[(min(u, v), max(u, v))] & 1

def nonplanar(mask):
    for five in itertools.combinations(V, 5):
        if all(has(mask, u, v) for u, v in itertools.combinations(five, 2)):
            return True
        w = next(x for x in V if x not in five)
        for u, v in itertools.combinations(five, 2):
            if has(mask, w, u) and has(mask, w, v) and all(
                    has(mask, a, b) for a, b in itertools.combinations(five, 2) if {a, b} != {u, v}):
                return True
    for left in itertools.combinations(V, 3):
        if 0 not in left:
            continue
        right = [x for x in V if x not in left]
        if all(has(mask, a, b) for a in left for b in right):
            return True
    return False

table = {}
for mask in range(1 << 15):
    cols = [frozenset(PAIRS[i]) for i in range(15) if mask >> i & 1]
    comm, _ = closure(6, cols)
    complete = len(comm) == len(cols) ** 2
    key = ('closure-complete' if complete else 'closure-incomplete',
           'nonplanar' if nonplanar(mask) else 'planar')
    table[key] = table.get(key, 0) + 1
for k in sorted(table):
    print(k, table[k])
