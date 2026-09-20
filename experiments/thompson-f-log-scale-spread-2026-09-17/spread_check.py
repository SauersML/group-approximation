#!/usr/bin/env python3
"""Sanity checks for thompson-f-near-eigenvectors-spread-pointer-size-over-log-scales.

States of the one-sided model R are pointed forests (T_0, T_1, ...; i) on roots 0,1,2,... with
finitely many nontrivial trees.  A window state (T_0..T_{m-1}; i) in S_n is the R-state with
leaves on roots >= m.  s = |T_i|, r = |T_{i+1}| (1 if i+1 >= m).  merge and right are total on R.

For a unit vector f >= 0 supported on S_n (Perron vector of the move graph, and random vectors):
  (a) <f,A_n f> == 2 a_right + 2 a_merge, a_g = sum_x f(x) f(g x)      (exact identity, float)
  (b) ||f - f o merge||^2 <= delta, ||f - f o right||^2 <= delta, delta = 4 - <f,A f>
  (c) for every t:  P(s <= t < s+r) <= ||f-h_m|| ||f+h_m||
                    P(r <= t) - P(s <= t) <= ||f-h_r|| ||f+h_r||
  (d) P(min(s,r) <= 2^J) <= 3 (J+1) * 2 sqrt(delta)                    for J = 0..4
Floating point; illustrations of a proved lemma, not certificates.
"""
import sys, math, random
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh

import os  # noqa: E402
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                                'thompson-f-forest-lossless-2026-09-17'))
from window_spectrum import forests, leaves  # noqa: E402


def run(n, vec_kind, rng):
    states = [(f, i) for f in forests(n) for i in range(len(f))]
    idx = {s: k for k, s in enumerate(states)}
    N = len(states)
    right = np.full(N, -1)
    merge = np.full(N, -1)
    s = np.zeros(N, dtype=int)
    r = np.zeros(N, dtype=int)
    rows, cols = [], []
    for k, (f, i) in enumerate(states):
        m = len(f)
        s[k] = leaves(f[i])
        r[k] = leaves(f[i + 1]) if i + 1 < m else 1
        nb = []
        if i + 1 < m:
            right[k] = idx[(f, i + 1)]
            merge[k] = idx[(f[:i] + ((f[i], f[i + 1]),) + f[i + 2:], i)]
            nb += [right[k], merge[k]]
        if i > 0:
            nb.append(idx[(f, i - 1)])
        if f[i] != ():
            nb.append(idx[(f[:i] + (f[i][0], f[i][1]) + f[i + 1:], i)])
        rows += [k] * len(nb)
        cols += nb
    A = coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(N, N)).tocsr()
    if vec_kind == 'perron':
        _, v = eigsh(A, k=1, which='LA', tol=1e-12)
        f = np.abs(v[:, 0])
    else:
        f = np.array([rng.random() ** 3 for _ in range(N)])
    f /= np.linalg.norm(f)
    q = float(f @ (A @ f))
    delta = 4 - q
    # in R, right/merge of a last-tree state leaves supp f  ->  value 0
    hr = np.where(right >= 0, f[np.maximum(right, 0)], 0.0)
    hm = np.where(merge >= 0, f[np.maximum(merge, 0)], 0.0)
    a_r, a_m = float(f @ hr), float(f @ hm)
    ok = abs(q - 2 * a_r - 2 * a_m) < 1e-9
    er, em = float(np.sum((f - hr) ** 2)), float(np.sum((f - hm) ** 2))
    ok &= er <= delta + 1e-9 and em <= delta + 1e-9
    cm = math.sqrt(em) * float(np.linalg.norm(f + hm))
    cr = math.sqrt(er) * float(np.linalg.norm(f + hr))
    p = f * f
    worst_m = worst_r = 0.0
    for t in range(1, n + 2):
        pm = float(p[(s <= t) & (t < s + r)].sum())
        pr = float(p[r <= t].sum() - p[s <= t].sum())
        worst_m, worst_r = max(worst_m, pm - cm), max(worst_r, pr - cr)
    ok &= worst_m <= 1e-9 and worst_r <= 1e-9
    for J in range(5):
        pj = float(p[np.minimum(s, r) <= 2 ** J].sum())
        ok &= pj <= 6 * (J + 1) * math.sqrt(max(delta, 0)) + 1e-9
    print("n=%d %-6s |S_n|=%6d quotient=%.6f delta=%.4f ||f-f.merge||^2=%.4f ||f-f.right||^2=%.4f "
          "P(s=1)=%.4f P(min<=2)=%.4f  %s" % (n, vec_kind, N, q, delta, em, er,
                                            float(p[s == 1].sum()),
                                            float(p[np.minimum(s, r) <= 2].sum()),
                                            "OK" if ok else "FAIL"))
    return ok


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    rng = random.Random(20260920)
    allok = True
    for n in range(2, nmax + 1):
        allok &= run(n, 'perron', rng)
        allok &= run(n, 'random', rng)
    print("ALL OK" if allok else "SOME FAIL")
