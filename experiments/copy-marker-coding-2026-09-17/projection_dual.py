"""Inspect the LP dual (a bounded test function phi) of the conjugation projection for A = B_1.

The dual of min TV(C mu, L mu) gives phi with |phi| <= 1/2 and
(1/K) sum_g [phi(g d g^-1) - phi(g d)] >= value for every d in B_n.
We tabulate phi against simple word statistics: conjugation depth k (D = u D' u^-1 with D'
cyclically reduced, k = |u|), core length |D'|, and length |D|.
Run: python3 projection_dual.py n
"""
import sys
from collections import defaultdict
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog
from coded_pair_lp import ball, mul, INV
from conjugation_projection_lp import inv


def depth(w):
    k = 0
    while len(w) >= 2 and w[0] == INV[w[-1]]:
        w = w[1:-1]; k += 1
    return k, len(w)


def main(n):
    S = ['', 'a', 'A', 'b', 'B']
    K = len(S)
    Bn = ball(n)
    cells, rows, cols, vals = {}, [], [], []
    for j, d in enumerate(Bn):
        for g in S:
            for c, s in ((mul(mul(g, d), inv(g)), 1.0), (mul(g, d), -1.0)):
                r = cells.setdefault(c, len(cells))
                rows.append(r); cols.append(j); vals.append(s / K)
    R, N = len(cells), len(Bn)
    D = sp.csr_matrix((vals, (rows, cols)), shape=(R, N))
    D.sum_duplicates()
    I = sp.identity(R, format='csr')
    Aub = sp.vstack([sp.hstack([D, -I]), sp.hstack([-D, -I])], format='csr')
    Aeq = sp.hstack([sp.csr_matrix(np.ones((1, N))), sp.csr_matrix((1, R))], format='csr')
    cst = np.concatenate([np.zeros(N), 0.5 * np.ones(R)])
    res = linprog(cst, A_ub=Aub, b_ub=np.zeros(2 * R), A_eq=Aeq, b_eq=[1.0],
                  bounds=[(0, None)] * (N + R), method='highs')
    lam = res.ineqlin.marginals
    phi = -(lam[:R] - lam[R:])  # test function on cells
    print('value', res.fun)
    cl = list(cells.keys())
    tab = defaultdict(list)
    for c, r in cells.items():
        k, core = depth(c)
        tab[(k, core)].append(phi[r])
    for key in sorted(tab):
        v = np.array(tab[key])
        print(key, len(v), round(v.min(), 3), round(v.mean(), 3), round(v.max(), 3))


if __name__ == '__main__':
    main(int(sys.argv[1]))
