"""Test the complex-phase inequality (**):
   for Hermitian zero-diagonal C with |C_ij| >= 1 on edges of G and C_ij = 0 off edges,
   ||D C D||_1 >= sqrt3 (W - alpha_w(G)),  D = diag(sqrt w).
Local minimisation of ratio ||DCD||_1/(W-alpha_w) over phases, moduli (>=1) and w.
usage: python complex_star.py seed N p trials"""
import sys, itertools, numpy as np
from scipy.optimize import minimize
seed, N, p, trials = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
rng = np.random.default_rng(seed)
def indep_sets(A):
    N = len(A); out = []
    for m in range(1, 1 << N):
        S = [i for i in range(N) if m >> i & 1]
        if all(A[i][j] == 0 for i in S for j in S if i < j): out.append(S)
    return out
best = (9, None)
for t in range(trials):
    if p >= 1: A = np.ones((N, N), int) - np.eye(N, dtype=int)
    else:
        A = np.triu((rng.random((N, N)) < p).astype(int), 1); A = A + A.T
    E = [(i, j) for i in range(N) for j in range(i + 1, N) if A[i, j]]
    if not E: continue
    I = indep_sets(A)
    def ratio(x):
        th = x[:len(E)]; r = 1 + x[len(E):2 * len(E)] ** 2; w = x[2 * len(E):] ** 2
        W = w.sum(); al = max(w[S].sum() for S in I)
        if W - al < 1e-9: return 9.0
        C = np.zeros((N, N), complex)
        for k, (i, j) in enumerate(E):
            C[i, j] = r[k] * np.exp(1j * th[k]); C[j, i] = np.conj(C[i, j])
        d = np.sqrt(w); M = d[:, None] * C * d[None, :]
        return np.abs(np.linalg.eigvalsh(M)).sum() / (np.sqrt(3) * (W - al))
    for rs in range(4):
        x0 = np.concatenate([rng.uniform(0, 2 * np.pi, len(E)), 0.1 * rng.standard_normal(len(E)), rng.uniform(0.3, 1, N)])
        res = minimize(ratio, x0, method='Nelder-Mead', options=dict(maxiter=20000, xatol=1e-9, fatol=1e-11))
        res = minimize(ratio, res.x, method='Powell')
        if res.fun < best[0]: best = (res.fun, (A.tolist(), np.round(res.x[2*len(E):]**2 / (res.x[2*len(E):]**2).sum(), 4).tolist()))
print(f"seed {seed} N {N} p {p} trials {trials}: min ||DCD||_1/(sqrt3 (W-alpha)) = {best[0]:.6f}")
print("  A, w:", best[1])
