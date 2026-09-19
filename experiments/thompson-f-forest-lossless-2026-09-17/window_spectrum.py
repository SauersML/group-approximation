#!/usr/bin/env python3
"""Top eigenvalue rho_n of the pointed-forest move graph on S_n (floating point, scipy eigsh).

By thompson-f-one-sided-forest-windows-are-norm-lossless, rho_n is nondecreasing and
rho_n -> ||K|| = 4||P||.  Also printed: the deficiency mass sum_v (4 - deg_n(v)) f(v)^2 of the unit
Perron vector f, where deg_n is the degree in the move graph on S_n (pointer at 0, pointer on a
leaf and pointer on the last window tree all lower it).  Since <f,Af> <= sum_v deg_n(v) f(v)^2,
rho_n <= 4 - deficiency mass.
Floating point only: these numbers are illustrations, not certificates.
"""
import sys
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh


def tree_codes(n, memo={}):
    """Trees with n leaves encoded as nested tuples; () is a leaf."""
    if n == 1:
        return [()]
    if n not in memo:
        memo[n] = [(l, r) for a in range(1, n) for l in tree_codes(a) for r in tree_codes(n - a)]
    return memo[n]


def leaves(t):
    return 1 if t == () else leaves(t[0]) + leaves(t[1])


def forests(n):
    out = []

    def rec(rem, pre):
        if rem == 0:
            out.append(tuple(pre))
            return
        for a in range(1, rem + 1):
            for t in tree_codes(a):
                pre.append(t)
                rec(rem - a, pre)
                pre.pop()
    rec(n, [])
    return out


def spectrum(n):
    states = [(f, i) for f in forests(n) for i in range(len(f))]
    idx = {s: k for k, s in enumerate(states)}
    rows, cols = [], []
    deg = np.zeros(len(states))
    for k, (f, i) in enumerate(states):
        m = len(f)
        nbrs = []
        if i + 1 < m:
            nbrs.append((f, i + 1))
            nbrs.append((f[:i] + ((f[i], f[i + 1]),) + f[i + 2:], i))
        if i > 0:
            nbrs.append((f, i - 1))
        if f[i] != ():
            nbrs.append((f[:i] + (f[i][0], f[i][1]) + f[i + 1:], i))
        deg[k] = len(nbrs)
        for y in nbrs:
            rows.append(k)
            cols.append(idx[y])
    N = len(states)
    A = coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(N, N)).tocsr()
    assert (A != A.T).nnz == 0
    if N == 1:
        return N, 0.0, 1.0
    vals, vecs = eigsh(A, k=1, which='LA', tol=1e-12)
    f = np.abs(vecs[:, 0])
    f /= np.linalg.norm(f)
    return N, vals[0], float(np.sum((4 - deg) * f * f))


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    for n in range(1, nmax + 1):
        N, rho, defm = spectrum(n)
        print("n=%2d |S_n|=%8d rho_n=%.9f rho_n/4=%.9f deficiency_mass=%.6f"
              % (n, N, rho, rho / 4, defm), flush=True)
