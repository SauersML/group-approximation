#!/usr/bin/env python3
"""Dirichlet (finite-window) certificates for ||P|| on Thompson's group F, and the
exchange rate between window radius and cogrowth word length.

For any finite A in the vertex set of Gamma = Cay(F, {x0^{+-1}, x1^{+-1}}) and any
real vector v supported on A,

    ||P|| >= <A_Gamma v, v> / (4 <v, v>),

and the best such vector is the top Dirichlet eigenvector of the induced subgraph.
Taking A = B_r (the ball of radius r) gives a bound that is comparable with the one
extracted from the closed-walk counts c_0..c_N: on the 4-regular tree the two agree
*exactly* when N = r, because there the top Dirichlet eigenvector of a ball is
radial and the radial subspace is the Krylov space of delta_e, whose Rayleigh
maximum is the largest Gauss node of the moment problem.  In F the ball can do
strictly better, and this script measures by how much.

Certificate discipline: the eigenvector is computed in floating point, then rounded
to integers, and the reported bound is the exact integer Rayleigh quotient
<A v, v> / (4 <v, v>) of the rounded vector (numerator and denominator are exact
int64/Python-int sums).  So the printed lower bound does not depend on the
eigensolver being correct.

Usage:  python3 ball_eigen.py RMAX [--out out.json]
"""
import argparse
import json
import os
import sys
import time

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import eigsh

sys.setrecursionlimit(10000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f_elements import TIDENT, TGENS, key, unkey, tmul  # noqa: E402
from ball_boundary import build_ball  # noqa: E402


def all_edges(keys, idx, level, rmax):
    """Every edge of Gamma with both endpoints in B_rmax, as index pairs i < j."""
    rows, cols = [], []
    for i, k in enumerate(keys):
        g = unkey(k)
        for s in TGENS:
            j = idx.get(key(tmul(g, s)))
            if j is not None and j > i:
                rows.append(i)
                cols.append(j)
    return np.array(rows, dtype=np.int64), np.array(cols, dtype=np.int64)


def exact_rayleigh(rows, cols, v):
    """Exact <A v, v> and <v, v> for an integer vector v."""
    v = v.astype(object)
    num = 2 * int(sum(v[rows] * v[cols]))
    den = int(sum(v * v))
    return num, den


def window_bound(rows, cols, n, scale=10 ** 4, k=1):
    A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(n, n))
    A = A + A.T
    if n <= 3:
        w = np.linalg.eigvalsh(A.toarray())
        vec = np.ones((n, 1))
        lam = w[-1]
    else:
        lam, vec = eigsh(A, k=k, which="LA", tol=1e-9, maxiter=5000)
        lam, vec = lam[-1], vec[:, -1:]
    x = np.abs(vec[:, 0])
    x = x / max(x.max(), 1e-300)
    iv = np.rint(x * scale).astype(np.int64)
    if not iv.any():
        iv = np.ones(n, dtype=np.int64)
    num, den = exact_rayleigh(rows, cols, iv)
    return float(lam), num, den


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("rmax", type=int)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    log = lambda s: print(s, file=sys.stderr, flush=True)  # noqa: E731

    t0 = time.time()
    keys, idx, level = build_ball(a.rmax, log)
    lv = np.array(level, dtype=np.int8)
    R, C = all_edges(keys, idx, level, a.rmax)
    log(f"edges of B_{a.rmax}: {len(R)} ({time.time()-t0:.0f}s)")
    res = []
    for r in range(2, a.rmax + 1):
        keep = (lv[R] <= r) & (lv[C] <= r)
        rows, cols = R[keep], C[keep]
        n = int((lv <= r).sum())
        lam, num, den = window_bound(rows, cols, len(keys))
        exact = num / (4 * den)
        res.append({"r": r, "ball": n, "edges": int(len(rows)),
                    "avg_inner_degree": 2 * len(rows) / n,
                    "lambda_max_over_4_float": lam / 4,
                    "certified_rayleigh_num": num, "certified_rayleigh_den": 4 * den,
                    "certified_lower_bound": exact})
        log(f"r={r}: |B_r|={n} lam/4={lam/4:.6f} certified {exact:.6f} ({time.time()-t0:.0f}s)")
    out = {"rmax": a.rmax, "windows": res, "seconds": round(time.time() - t0, 1)}
    text = json.dumps(out, indent=1)
    if a.out:
        open(a.out, "w").write(text + "\n")
    else:
        print(text)


if __name__ == "__main__":
    main()
