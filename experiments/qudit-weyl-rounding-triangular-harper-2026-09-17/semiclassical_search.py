"""Semiclassical (small-angle Gaussian) ratio rho(w, Omega) = 4 (W - m_iso) / ||D Omega D||_1 for k Weyl directions
with integer symplectic Gram matrix Omega (entries in {-1,0,1}), D = diag(sqrt w). c_d ~ (d/2pi) rho.
Exhaustive over Omega up to k=5, random for k=6,7; weights optimized by Nelder-Mead from random starts."""
import itertools, sys
import numpy as np
from scipy.optimize import minimize
rng = np.random.default_rng(0)
def m_iso(w, Om):
    k = len(w); best = 0
    for mask in range(1, 1 << k):
        idx = [i for i in range(k) if mask >> i & 1]
        if all(Om[i, j] == 0 for i in idx for j in idx if i < j):
            best = max(best, sum(w[i] for i in idx))
    return best
def rho(x, Om):
    x = np.clip(x, -8, 8); w = np.exp(x); D = np.sqrt(w)
    M = D[:, None] * Om * D[None, :]
    nn = np.sum(np.abs(np.linalg.eigvals(M)))
    return 4 * (w.sum() - m_iso(w, Om)) / nn if nn > 1e-12 else 0
best_overall = {}
KS = [int(a) for a in sys.argv[1:]] or list(range(2, 8))
for k in KS:
    pairs = list(itertools.combinations(range(k), 2))
    if 3 ** len(pairs) <= 60000:
        pats = itertools.product([-1, 0, 1], repeat=len(pairs))
    else:
        pats = (tuple(rng.integers(-1, 2, len(pairs))) for _ in range(20000))
    best = (0, None, None)
    for p in pats:
        if p[0] == -1: continue            # sign symmetry
        Om = np.zeros((k, k))
        for (i, j), s in zip(pairs, p):
            Om[i, j] = s; Om[j, i] = -s
        if np.any(np.all(Om == 0, axis=1)): continue   # isolated direction is useless
        r0 = rho(np.zeros(k), Om)
        if r0 < best[0] - 0.6: continue
        for t in range(2):
            x0 = rng.normal(scale=0.3, size=k) if t else np.zeros(k)
            res = minimize(lambda x: -rho(x, Om), x0, method='Nelder-Mead', options={'maxiter': 400, 'xatol': 1e-5, 'fatol': 1e-8})
            if -res.fun > best[0]:
                best = (-res.fun, Om.copy(), np.exp(np.clip(res.x, -8, 8)) / np.exp(np.clip(res.x, -8, 8)).max())
    print(f"k={k}: best rho={best[0]:.5f} (4/sqrt3={4/np.sqrt(3):.5f}, 2sqrt2={2*np.sqrt(2):.5f})\nOmega=\n{best[1]}\nweights={np.round(best[2], 4)}", flush=True)
