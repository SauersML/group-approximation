"""Symmetry-reduced version of conjugation_projection_lp.py for A = B_1 (8 signed permutations).
Run: python3 conjugation_projection_sym.py n1 n2 ...
"""
import sys
import time
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog
from coded_pair_lp import ball, mul
from coded_pair_lp_sym import MAPS
from conjugation_projection_lp import inv


def canon(w):
    return min(w.translate(t) for t in MAPS)


def solve(n, Aset=('', 'a', 'A', 'b', 'B'), return_dual=False):
    K = len(Aset)
    Bn = ball(n)
    var, size = {}, []
    for d in Bn:
        c = canon(d)
        if c not in var:
            var[c] = len(var); size.append(0)
        size[var[c]] += 1
    reps = list(var.keys())
    cellrow, cellwt = {}, []
    rows, cols, vals = [], [], []
    # residual at a cell c is invariant; sum over cells = sum over cell orbits * orbit size.
    # Compute residual vector of one representative d per variable orbit, scaled by orbit size,
    # then map cells to canonical cells: sum_{d in orbit} (C - L) delta_d, canonicalized, equals
    # size * canon-image; the residual at canonical cell c equals total mass / orbit size of c.
    # Simpler: enumerate all d, canonicalize each image cell, and record per-variable entries.
    for d in Bn:
        v = var[canon(d)]
        for g in Aset:
            for w, s in ((mul(mul(g, d), inv(g)), 1.0), (mul(g, d), -1.0)):
                c = canon(w)
                if c not in cellrow:
                    cellrow[c] = len(cellrow); cellwt.append(0)
                rows.append(cellrow[c]); cols.append(v); vals.append(s / K)
    # count orbit sizes of cells
    orbit = {}
    for c in cellrow:
        orbit[c] = len({c.translate(t) for t in MAPS})
    R = len(cellrow)
    nv = len(var)
    # summed-over-orbit residual M; residual per cell = M / orbit; objective 0.5*sum orbit*|M/orbit| = 0.5*sum |M|
    D = sp.csr_matrix((vals, (rows, cols)), shape=(R, nv))
    D.sum_duplicates()
    I = sp.identity(R, format='csr')
    Aub = sp.vstack([sp.hstack([D, -I]), sp.hstack([-D, -I])], format='csr')
    # variable x_v is the common value nu(d) for d in the orbit; the D above sums over all d in orbit
    Aeq = sp.hstack([sp.csr_matrix(np.array(size, float).reshape(1, -1)), sp.csr_matrix((1, R))], format='csr')
    cst = np.concatenate([np.zeros(nv), 0.5 * np.ones(R)])
    res = linprog(cst, A_ub=Aub, b_ub=np.zeros(2 * R), A_eq=Aeq, b_eq=[1.0],
                  bounds=[(0, None)] * (nv + R), method='highs')
    return res.fun, nv, R


if __name__ == '__main__':
    for n in [int(a) for a in sys.argv[1:]]:
        t = time.time()
        val, nv, R = solve(n)
        print(f'proj B_1 sym n={n} vars={nv} rows={R} minTV={val:.6f} time={time.time()-t:.0f}s', flush=True)
