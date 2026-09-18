"""Copy-marker coded pair in F_2 x F_2: minimal TV(alpha nu, beta nu) over nu in P(B_n x B_n).

alpha = uniform law of (g, g), beta = uniform law of (e, g), g uniform on A in F_2.
alpha nu = law(gY, gZ), beta nu = law(Y, gZ) for nu = law(Y, Z), g independent.
Run: python3 coded_pair_lp.py [nmax]
"""
import sys
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog

GENS = ['a', 'A', 'b', 'B']  # A = a^-1, B = b^-1
INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def mul(u, v):
    """Product of reduced words u*v (strings)."""
    u = list(u)
    for ch in v:
        if u and u[-1] == INV[ch]:
            u.pop()
        else:
            u.append(ch)
    return ''.join(u)


def ball(n):
    out = ['']
    frontier = ['']
    for _ in range(n):
        nxt = []
        for w in frontier:
            for ch in GENS:
                if not w or w[-1] != INV[ch]:
                    nxt.append(w + ch)
        out += nxt
        frontier = nxt
    return out


def min_tv(Aset, n):
    Bn = ball(n)
    idx = {w: i for i, w in enumerate(Bn)}
    N = len(Bn)
    K = len(Aset)
    # target cells
    cells = {}
    rows, cols, vals = [], [], []
    for i, y in enumerate(Bn):
        for j, z in enumerate(Bn):
            v = i * N + j
            for g in Aset:
                ca = (mul(g, y), mul(g, z))  # alpha: (gY, gZ)
                cb = (y, mul(g, z))          # beta: (Y, gZ)
                for c, s in ((ca, 1.0), (cb, -1.0)):
                    r = cells.setdefault(c, len(cells))
                    rows.append(r); cols.append(v); vals.append(s / K)
    R = len(cells)
    D = sp.csr_matrix((vals, (rows, cols)), shape=(R, N * N))
    D.sum_duplicates()
    # variables: nu (N^2), t (R); minimize 0.5 * sum t
    nv = N * N
    I = sp.identity(R, format='csr')
    Aub = sp.vstack([sp.hstack([D, -I]), sp.hstack([-D, -I])], format='csr')
    bub = np.zeros(2 * R)
    Aeq = sp.hstack([sp.csr_matrix(np.ones((1, nv))), sp.csr_matrix((1, R))], format='csr')
    c = np.concatenate([np.zeros(nv), 0.5 * np.ones(R)])
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=[1.0],
                  bounds=[(0, None)] * (nv + R), method='highs')
    return res.fun, N


if __name__ == '__main__':
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    sets = {
        '{e,a}': ['', 'a'],
        '{e,a,b}': ['', 'a', 'b'],
        '{a,b}': ['a', 'b'],
        'B_1': ['', 'a', 'A', 'b', 'B'],
        '{a,A,b,B}': ['a', 'A', 'b', 'B'],
    }
    for name, S in sets.items():
        for n in range(0, nmax + 1):
            val, N = min_tv(S, n)
            print(f'{name:10s} n={n} |B_n|={N:4d} minTV={val:.6f}', flush=True)
