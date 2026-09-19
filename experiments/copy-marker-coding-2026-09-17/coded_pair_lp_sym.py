"""Symmetry-reduced LP for the copy-marker coded pair of A = B_1 in F_2 x F_2.

Same quantity as coded_pair_lp.py (min over nu in P(B_n x B_n) of TV(alpha nu, beta nu)),
restricted w.l.o.g. to nu invariant under the 8 automorphisms of F_2 that permute {a,A,b,B}
(signed generator permutations), acting diagonally. A = B_1 is invariant, so alpha and beta
are too, and averaging an optimum over the group gives an invariant optimum.
Run: python3 coded_pair_lp_sym.py n
"""
import sys
import time
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog
from coded_pair_lp import ball, mul

MAPS = []
for swap in (False, True):
    for ia in (False, True):
        for ib in (False, True):
            m = {'a': 'a', 'A': 'A', 'b': 'b', 'B': 'B'}
            if ia:
                m['a'], m['A'] = 'A', 'a'
            if ib:
                m['b'], m['B'] = 'B', 'b'
            if swap:
                m = {k: {'a': 'b', 'A': 'B', 'b': 'a', 'B': 'A'}[v] for k, v in m.items()}
            MAPS.append(str.maketrans(m))


def canon(y, z):
    return min((y.translate(t), z.translate(t)) for t in MAPS)


def solve(n, Aset=('', 'a', 'A', 'b', 'B')):
    K = len(Aset)
    Bn = ball(n)
    inball = set(Bn)
    var = {}
    size = []
    for y in Bn:
        for z in Bn:
            c = canon(y, z)
            if c not in var:
                var[c] = len(var)
                size.append(0)
            size[var[c]] += 1
    Bn1 = ball(n + 1)
    rows, cols, vals, wts = [], [], [], []
    seen = {}
    r = 0
    for x in Bn1:
        for w in Bn1:
            c = canon(x, w)
            if c in seen:
                seen[c] += 1
                continue
            seen[c] = 1
            x0, w0 = c
            entries = {}
            for g in Aset:
                gi = ''.join({'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}[ch] for ch in reversed(g))
                y, z = mul(gi, x0), mul(gi, w0)   # alpha: nu(g^-1 x, g^-1 w)
                if y in inball and z in inball:
                    v = var[canon(y, z)]
                    entries[v] = entries.get(v, 0.0) + 1.0 / K
                if x0 in inball and z in inball:  # beta: nu(x, g^-1 w)
                    v = var[canon(x0, z)]
                    entries[v] = entries.get(v, 0.0) - 1.0 / K
            entries = {k: v for k, v in entries.items() if abs(v) > 1e-15}
            if not entries:
                seen[c] = -1
                continue
            for k, v in entries.items():
                rows.append(r); cols.append(k); vals.append(v)
            wts.append(c)
            r += 1
    R = r
    wt = np.array([seen[c] for c in wts], dtype=float)
    nv = len(var)
    D = sp.csr_matrix((vals, (rows, cols)), shape=(R, nv))
    I = sp.identity(R, format='csr')
    Aub = sp.vstack([sp.hstack([D, -I]), sp.hstack([-D, -I])], format='csr')
    Aeq = sp.hstack([sp.csr_matrix(np.array(size, dtype=float).reshape(1, -1)),
                     sp.csr_matrix((1, R))], format='csr')
    cst = np.concatenate([np.zeros(nv), 0.5 * wt])
    res = linprog(cst, A_ub=Aub, b_ub=np.zeros(2 * R), A_eq=Aeq, b_eq=[1.0],
                  bounds=[(0, None)] * (nv + R), method='highs')
    return res.fun, nv, R


if __name__ == '__main__':
    for n in [int(a) for a in sys.argv[1:]]:
        t = time.time()
        val, nv, R = solve(n)
        print(f'B_1 sym n={n} vars={nv} rows={R} minTV={val:.6f} time={time.time()-t:.0f}s', flush=True)
