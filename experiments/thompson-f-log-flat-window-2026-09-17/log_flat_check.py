#!/usr/bin/env python3
"""Sanity checks for thompson-f-near-eigenvectors-are-log-flat-near-the-pointer.

Model: one-sided pointed forests R (see thompson-f-one-sided-forest-windows-are-norm-lossless).
A window state (T_0..T_{m-1}; i) in S_n is the R-state whose trees on roots >= m are leaves.
Sizes s_j = |T_{i+j}| (1 beyond the window).  right and merge are total on R; for a window vector
f (supported on S_n) the pushed vectors h = f o right, f o merge vanish where the move leaves S_n.

For a unit f >= 0 on S_n (Perron vector of the move graph, and a random vector) with
delta = 4 - <f, A f>, let c_R = ||f - f o right|| ||f + f o right||, c_M the same for merge
(both <= 2 sqrt(delta), Step 2 of the log-scale spread route).  Checked, for offsets j = 0..3:
  (a) P(s_j <= t < s_j + s_{j+1})       <= c_M + j c_R           every integer t (sizes are integers)
  (b) P(s_{j+1} <= t < s_{j+1} + s_j)   <= c_M + (j+1) c_R
  (c) Fubini: E ln(min(s_j+s_{j+1},T)/min(s_j,T)) = sum_{k<T} P(s_j <= k < s_j+s_{j+1}) ln((k+1)/k)
  (d) E |ln(s_j ^ T) - ln(s_{j+1} ^ T)| <= (2 c_M + (2j+1) c_R) ln T     for T = 2..n+2
  (e) window: E sum_{m<W} |L_{m+1} - L_m| <= sum_{m<W} (2 c_M + (2m+1) c_R) ln T,  L_m = ln(s_m ^ T)
Also printed: the normalized gap gamma_T = E|L_0 - L_1| / ln T and the implied floor (gamma/6)^2.
Floating point; these illustrate a proved chain of inequalities, they are not certificates.
At these n delta is large, so the bounds are far from tight.
"""
import sys, math, random, os
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                                'thompson-f-forest-lossless-2026-09-17'))
from window_spectrum import forests, leaves  # noqa: E402

JMAX = 3
W = 4
EPS = 1e-9


def run(n, kind, rng):
    states = [(f, i) for f in forests(n) for i in range(len(f))]
    idx = {s: k for k, s in enumerate(states)}
    N = len(states)
    right = np.full(N, -1)
    merge = np.full(N, -1)
    size = np.ones((N, JMAX + W + 2), dtype=int)
    rows, cols = [], []
    for k, (f, i) in enumerate(states):
        m = len(f)
        for j in range(size.shape[1]):
            if i + j < m:
                size[k, j] = leaves(f[i + j])
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
    if kind == 'perron':
        _, v = eigsh(A, k=1, which='LA', tol=1e-12)
        f = np.abs(v[:, 0])
    else:
        f = np.array([rng.random() ** 3 for _ in range(N)])
    f /= np.linalg.norm(f)
    delta = 4 - float(f @ (A @ f))
    hr = np.where(right >= 0, f[np.maximum(right, 0)], 0.0)
    hm = np.where(merge >= 0, f[np.maximum(merge, 0)], 0.0)
    cR = float(np.linalg.norm(f - hr) * np.linalg.norm(f + hr))
    cM = float(np.linalg.norm(f - hm) * np.linalg.norm(f + hm))
    ok = cR <= 2 * math.sqrt(delta) + EPS and cM <= 2 * math.sqrt(delta) + EPS
    p = f * f
    worst = 0.0
    for j in range(JMAX + 1):
        a, b = size[:, j], size[:, j + 1]
        for t in range(1, n + 3):
            worst = max(worst, float(p[(a <= t) & (t < a + b)].sum()) - (cM + j * cR))
            worst = max(worst, float(p[(b <= t) & (t < a + b)].sum()) - (cM + (j + 1) * cR))
        for T in range(2, n + 3):
            lhs = float(p @ np.log(np.minimum(a + b, T) / np.minimum(a, T)))
            fub = sum(float(p[(a <= k) & (k < a + b)].sum()) * math.log((k + 1) / k)
                      for k in range(1, T))
            ok &= abs(lhs - fub) < 1e-9
            gap = float(p @ np.abs(np.log(np.minimum(a, T)) - np.log(np.minimum(b, T))))
            worst = max(worst, gap / math.log(T) - (2 * cM + (2 * j + 1) * cR))
    for T in range(2, n + 3):
        L = np.log(np.minimum(size[:, :W + 1], T))
        tot = float(p @ np.abs(np.diff(L, axis=1)).sum(axis=1))
        bound = sum(2 * cM + (2 * m + 1) * cR for m in range(W)) * math.log(T)
        worst = max(worst, tot - bound)
    ok &= worst <= EPS
    T = n + 2
    gam = float(p @ np.abs(np.log(np.minimum(size[:, 0], T)) - np.log(np.minimum(size[:, 1], T)))) \
        / math.log(T)
    print("n=%d %-6s |S_n|=%6d delta=%.4f cR=%.4f cM=%.4f gamma_T(T=%d)=%.4f (gamma/6)^2=%.5f "
          "worst slack=%.3e %s" % (n, kind, N, delta, cR, cM, T, gam, (gam / 6) ** 2, worst,
                                   "OK" if ok else "FAIL"))
    return ok


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    rng = random.Random(20260920)
    allok = True
    for n in range(2, nmax + 1):
        for kind in ('perron', 'random'):
            allok &= run(n, kind, rng)
    print("ALL OK" if allok else "SOME FAIL")
