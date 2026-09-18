#!/usr/bin/env python3
"""Minimal-window LP for an arbitrary linear entropy expression over a Z configuration.

min over polymatroids satisfying (P), (I), (D), (T) of  sum_i c_i h(S_i).
A minimum >= 0 means the inequality  sum c_i h(S_i) >= 0  has a Shannon-type derivation on the window.

Items are written 'x3', 'y-1'. Mutual informations are expanded by mi(A, B, C).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'shannon-window-certificates-2026-09-17'))
import numpy as np
from scipy.optimize import linprog
from shannon_lp import Zd, build, constraints

G = Zd(1)


def item(s):
    return (s[0], (int(s[1:]),))


def mi(A, B, C=()):
    """I(A;B|C) as a list of (coef, items)."""
    A, B, C = list(A), list(B), list(C)
    return [(1, A + C), (1, B + C), (-1, A + B + C), (-1, C)]


def minimize(E, F, terms, X=None, Y=None):
    d = build(G, [(e,) for e in E], [(f,) for f in F],
              X=None if X is None else [(g,) for g in X], Y=None if Y is None else [(g,) for g in Y])
    A_ub, b_ub, A_eq, b_eq, _ = constraints(d)
    c = np.zeros(d['nv'])
    for coef, its in terms:
        m = 0
        for s in its:
            m |= 1 << d['idx'][item(s)]
        c[d['col'][m]] += coef
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method='highs-ipm')
    return res.fun, d


def ordered_split(E, F):
    """RHS - LHS of  I(x0 ; y_F) <= sum_{f reader} I(x0 ; y_f | x_{P_f})."""
    yF = ['y%d' % f for f in F]
    terms = [(-c, s) for c, s in mi(['x0'], yF)]
    for f in F:
        if -f in E:
            P = ['x%d' % (f + e) for e in E if f + e < 0]
            terms += mi(['x0'], ['y%d' % f], P)
    return terms


if __name__ == '__main__':
    E = [int(t) for t in sys.argv[1].split(',')]
    F = [int(t) for t in sys.argv[2].split(',')]
    val, d = minimize(E, F, ordered_split(E, F))
    print('E=%s F=%s n=%d ordered-split min(RHS-LHS)=%.6f' % (E, F, d['n'], val))
