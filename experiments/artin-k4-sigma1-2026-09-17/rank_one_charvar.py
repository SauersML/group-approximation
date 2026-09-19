#!/usr/bin/env python3
"""Exact rank-one (abelian) twisted Alexander test for A_K.

Phi(u_i) = x_i, Phi(v_j) = y_j (commuting variables).  The Fox matrix J(x,y)
is 6x4.  V1 = {rank J <= 2} is cut out by the 3x3 minors.  The chi-line through
(x,y) is (x t, y / t).  [chi] is detected by a rank-one twist iff V1 contains a
whole chi-line, i.e. iff every 3x3 minor vanishes identically in t after the
substitution x -> x t, y -> y/t at some point (x,y).
"""
import sympy as sp

x1, x2, y1, y2, t = sp.symbols('x1 x2 y1 y2 t')
G = {0: x1, 1: x2, 2: y1, 3: y2}


def braid(a, b, m):
    X = [a if k % 2 == 0 else b for k in range(m)]
    Y = [b if k % 2 == 0 else a for k in range(m)]
    return [(g, 1) for g in X] + [(g, -1) for g in reversed(Y)]


RELS = [braid(0, 1, 2), braid(2, 3, 2), braid(0, 2, 4), braid(1, 2, 4),
        braid(1, 3, 4), braid(0, 3, 6)]


def fox(r, i):
    pref = sp.Integer(1)
    out = sp.Integer(0)
    for g, e in r:
        if e == 1:
            if g == i:
                out += pref
            pref = pref * G[g]
        else:
            pref = pref / G[g]
            if g == i:
                out -= pref
    return sp.factor(sp.simplify(out))


J = sp.Matrix(6, 4, lambda j, i: fox(RELS[j], i))
if __name__ == "__main__":
    sp.pprint(J)
    # substitute the chi-line and ask for common zeros of all 3x3 minors
    Jt = J.subs({x1: x1 * t, x2: x2 * t, y1: y1 / t, y2: y2 / t})
    import itertools
    minors = []
    for rows in itertools.combinations(range(6), 3):
        for cols in itertools.combinations(range(4), 3):
            m = sp.factor(Jt.extract(list(rows), list(cols)).det())
            if m != 0:
                minors.append(m)
    print("nonzero 3x3 minors:", len(minors))
    # coefficients in t of each minor (numerators) must vanish
    eqs = set()
    for m in minors:
        num = sp.numer(sp.together(m))
        for c in sp.Poly(sp.expand(num), t).coeffs():
            eqs.add(sp.factor(c))
    print("number of t-coefficient equations:", len(eqs))
    GB = sp.groebner(list(eqs) + [x1 * x2 * y1 * y2 * sp.Symbol('z') - 1],
                     x1, x2, y1, y2, sp.Symbol('z'), order='grevlex')
    print("Groebner basis of chi-line locus (with x,y invertible):")
    print(GB)
