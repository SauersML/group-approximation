"""Projection of the coded pair under (x, w) -> w x^{-1}.

alpha nu -> law(g D g^{-1}), beta nu -> law(g D) with D = Z Y^{-1}, g uniform on A.
Push-forward contracts TV, so min_mu TV(C mu, L mu) is a lower bound for the coded pair
at the same window (D ranges over B_{2n} when Y, Z range over B_n).
Here C mu = (1/K) sum_g g mu g^{-1} and L mu = (1/K) sum_g g mu, mu in P(B_n).
Run: python3 conjugation_projection_lp.py nmax
"""
import sys
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog
from coded_pair_lp import ball, mul, INV


def inv(w):
    return ''.join(INV[ch] for ch in reversed(w))


def min_tv(Aset, n):
    Bn = ball(n)
    K = len(Aset)
    cells = {}
    rows, cols, vals = [], [], []
    for j, d in enumerate(Bn):
        for g in Aset:
            for c, s in ((mul(mul(g, d), inv(g)), 1.0), (mul(g, d), -1.0)):
                r = cells.setdefault(c, len(cells))
                rows.append(r); cols.append(j); vals.append(s / K)
    R = len(cells)
    N = len(Bn)
    D = sp.csr_matrix((vals, (rows, cols)), shape=(R, N))
    I = sp.identity(R, format='csr')
    Aub = sp.vstack([sp.hstack([D, -I]), sp.hstack([-D, -I])], format='csr')
    Aeq = sp.hstack([sp.csr_matrix(np.ones((1, N))), sp.csr_matrix((1, R))], format='csr')
    cst = np.concatenate([np.zeros(N), 0.5 * np.ones(R)])
    res = linprog(cst, A_ub=Aub, b_ub=np.zeros(2 * R), A_eq=Aeq, b_eq=[1.0],
                  bounds=[(0, None)] * (N + R), method='highs')
    return res.fun, res.x[:N], Bn


if __name__ == '__main__':
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for name, S in (('B_1', ['', 'a', 'A', 'b', 'B']), ('{e,a,b}', ['', 'a', 'b'])):
        for n in range(0, nmax + 1):
            val, mu, Bn = min_tv(S, n)
            print(f'{name:8s} n={n} |B_n|={len(Bn)} minTV={val:.6f}', flush=True)
