#!/usr/bin/env python3
"""Rank-one chi-line locus over GF(p) for small p (see rank_one_charvar.py)."""
import itertools, sys
import sympy as sp
from rank_one_charvar import J, x1, x2, y1, y2, t
z = sp.Symbol('z')
Jt = J.subs({x1: x1 * t, x2: x2 * t, y1: y1 / t, y2: y2 / t})
eqs = set()
for rows in itertools.combinations(range(6), 3):
    for cols in itertools.combinations(range(4), 3):
        m = sp.together(Jt.extract(list(rows), list(cols)).det())
        num = sp.expand(sp.numer(m))
        if num != 0:
            for c in sp.Poly(num, t).coeffs():
                eqs.add(sp.expand(c))
for p in [2, 3, 5, 7, 11, 13]:
    GB = sp.groebner(list(eqs) + [x1 * x2 * y1 * y2 * z - 1], x1, x2, y1, y2, z,
                     order='grevlex', modulus=p)
    print(p, list(GB.exprs)[:6], flush=True)
