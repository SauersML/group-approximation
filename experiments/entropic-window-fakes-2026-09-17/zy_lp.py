#!/usr/bin/env python3
"""Minimal-window LP for a cyclic configuration, with all unconditional Zhang-Yeung instances added.

usage: zy_lp.py n 'E' 'F'
For every assignment of ground-set variables to roles A, B, C, D or unused (A..D nonempty),
adds the (valid, unconditional) Zhang-Yeung inequality
  2 I(C;D) <= I(A;B) + I(A;CD) + 3 I(C;D|A) + I(C;D|B).
No conditional instances are added.  Prints the Shannon LP value and the Shannon+ZY LP value.
"""
import sys, os, itertools
import numpy as np
from scipy.sparse import coo_matrix, vstack
from scipy.optimize import linprog
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-window-certificates-2026-09-17'))
from random_scan import Cyc
from shannon_lp import build, constraints, objective


def zy_rows(d):
    n, col = d['n'], d['col']
    rows, cols, vals = [], [], []
    r = 0
    seen = set()
    for assign in itertools.product(range(5), repeat=n):  # 0..3 = A,B,C,D ; 4 = unused
        m = [0] * 5
        for i, a in enumerate(assign):
            m[a] |= 1 << i
        A, B, C, D = m[:4]
        if not (A and B and C and D):
            continue
        def I(P, Q, K=0):
            return [(P | K, 1), (Q | K, 1), (P | Q | K, -1), (K, -1)]
        # lhs - rhs <= 0
        terms = [(t, 2 * v) for t, v in I(C, D)]
        terms += [(t, -v) for t, v in I(A, B)]
        terms += [(t, -v) for t, v in I(A, C | D)]
        terms += [(t, -3 * v) for t, v in I(C, D, A)]
        terms += [(t, -v) for t, v in I(C, D, B)]
        acc = {}
        for t, v in terms:
            if t == 0:
                continue
            c = col[t]
            acc[c] = acc.get(c, 0) + v
        key = tuple(sorted((c, v) for c, v in acc.items() if v))
        if not key or key in seen:
            continue
        seen.add(key)
        for c, v in key:
            rows.append(r); cols.append(c); vals.append(float(v))
        r += 1
    return coo_matrix((vals, (rows, cols)), shape=(r, d['nv'])).tocsr()


if __name__ == '__main__':
    n = int(sys.argv[1]); E = [int(t) for t in sys.argv[2].split(',')]; F = [int(t) for t in sys.argv[3].split(',')]
    d = build(Cyc(n), E, F)
    A_ub, b_ub, A_eq, b_eq, _ = constraints(d)
    c = objective(d)
    r0 = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method='highs')
    Z = zy_rows(d)
    A2 = vstack([A_ub, Z]).tocsr()
    b2 = np.concatenate([b_ub, np.zeros(Z.shape[0])])
    r1 = linprog(c, A_ub=A2, b_ub=b2, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method='highs')
    print('n=%d E=%s F=%s ground=%d  Shannon LP %.6f   Shannon+ZY (%d rows) LP %.6f' % (
        n, E, F, d['n'], r0.fun, Z.shape[0], r1.fun))
