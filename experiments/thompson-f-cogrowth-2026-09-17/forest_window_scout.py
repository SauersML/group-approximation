#!/usr/bin/env python3
"""Scouting (floating point, NOT a certificate): Dirichlet eigenvalues of finite marked-forest
sets in the Cayley graph of F, as a possible alternative to moment certificates.

Why. For any finite vertex set S of the Cayley graph (generators x0^{+-1}, x1^{+-1}),
lambda_max(A_S)/4 <= ||P||, because A_S is a compression of 4P. An integer test vector f with
<f, A_S f> / (4 <f, f>) > 0.910677 would beat the moment bound certified in epg_certify.py.

Model. Conjugate F to G_R acting on R, generators s0 = t+1 and s1 = (t<=0: t; [0,1]: 2t; t>=1: t+1).
A state is a forest (T_0..T_{m-1}) of finite rooted binary trees with n leaves in total and a
pointer i. Right multiplication by the generators acts by
    s0      : pointer i -> i+1            (leaves the window at i = m-1)
    s0^-1   : pointer i -> i-1            (leaves the window at i = 0)
    s1      : merge T_i, T_{i+1}           (leaves the window at i = m-1)
    s1^-1   : split T_i = (A, B), pointer on A   (leaves the window if T_i is a leaf)
S_n = all states with n leaves (optionally all trees of height <= kmax). Edges inside S_n are the
moves above; the adjacency is symmetric (asserted).

Output: JSON table of (kmax, n, |S|, average inner degree, lambda_max/4) and the trend analysis.
"""
import json, sys, time
from functools import lru_cache
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh

E = ()


@lru_cache(None)
def trees(n):
    if n == 1:
        return [E]
    return [(a, b) for k in range(1, n) for a in trees(k) for b in trees(n - k)]


@lru_cache(None)
def forests(n):
    if n == 0:
        return [()]
    return [(t,) + f for k in range(1, n + 1) for t in trees(k) for f in forests(n - k)]


def height(t):
    return 0 if t == E else 1 + max(height(t[0]), height(t[1]))


def build(n, kmax=None):
    states = [(f, i) for f in forests(n)
              if kmax is None or all(height(t) <= kmax for t in f) for i in range(len(f))]
    idx = {s: j for j, s in enumerate(states)}
    rows, cols = [], []
    for j, (f, i) in enumerate(states):
        m = len(f)
        nb = []
        if i + 1 < m:
            nb.append((f, i + 1))
            nb.append((f[:i] + ((f[i], f[i + 1]),) + f[i + 2:], i))
        if i > 0:
            nb.append((f, i - 1))
        if f[i] != E:
            nb.append((f[:i] + (f[i][0], f[i][1]) + f[i + 1:], i))
        for s in nb:
            k = idx.get(s)
            if k is not None:
                rows.append(j)
                cols.append(k)
    A = sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(states), len(states)))
    return states, A


def lam(A):
    if A.shape[0] <= 50:
        return float(np.linalg.eigvalsh(A.toarray())[-1])
    return float(eigsh(A, k=1, which='LA')[0][0])


def run(kmax, ns):
    rows = []
    for n in ns:
        t0 = time.time()
        st, A = build(n, kmax)
        assert (A != A.T).nnz == 0
        r = {"kmax": kmax, "n": n, "states": len(st), "avg_inner_degree": float(A.sum() / len(st)),
             "lambda_over_4": lam(A) / 4, "seconds": round(time.time() - t0, 1)}
        print(r, file=sys.stderr, flush=True)
        rows.append(r)
    return rows


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    out = {"note": "floating point scouting only; nothing here is a certificate"}
    unb = run(None, range(2, nmax + 1))
    out["unbounded_height"] = unb
    out["height_le_2"] = run(2, range(4, nmax + 4))
    out["height_le_3"] = run(3, range(4, nmax + 2))
    # trend for unbounded heights: n^2 * (lambda_n - lambda_{n-1})
    lv = [r["lambda_over_4"] for r in unb]
    ns = [r["n"] for r in unb]
    c = [ns[j] ** 2 * (lv[j] - lv[j - 1]) for j in range(1, len(lv))]
    C = c[-1]
    tail = sum(1.0 / k ** 2 for k in range(ns[-1] + 1, 10 ** 6))
    limit = lv[-1] + C * tail
    need, acc = None, lv[-1]
    if limit > 0.910677:
        for n in range(ns[-1] + 1, 10 ** 6):
            acc += C / n ** 2
            if acc > 0.910677:
                need = n
                break
    out["trend_unbounded"] = {
        "n2_times_increment": c,
        "fitted_C": C,
        "extrapolated_limit_if_increments_C_over_n2": limit,
        "n_needed_to_exceed_0.910677_under_that_fit": need,
        "states_ratio_last": unb[-1]["states"] / unb[-2]["states"],
    }
    for key in ("height_le_2", "height_le_3"):
        lv2 = [r["lambda_over_4"] for r in out[key]]
        d = [lv2[j] - lv2[j - 1] for j in range(1, len(lv2))]
        q = d[-1] / d[-2]
        out["trend_" + key] = {"increments": d, "last_increment_ratio": q,
                               "geometric_tail_extrapolated_limit": lv2[-1] + d[-1] * q / (1 - q)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
