"""Complete graph K_m, uniform weights: min ||C||_1 over Hermitian zero-diagonal C with
|C_ij| >= 1 (local search over phases and moduli), against sqrt3 (m-1) needed by (**)."""
import numpy as np, sys
from scipy.optimize import minimize
rng = np.random.default_rng(3)
for m in range(3, int(sys.argv[1]) + 1):
    E = [(i, j) for i in range(m) for j in range(i + 1, m)]
    def f(x):
        C = np.zeros((m, m), complex)
        for k, (i, j) in enumerate(E):
            C[i, j] = (1 + x[len(E) + k] ** 2) * np.exp(1j * x[k]); C[j, i] = np.conj(C[i, j])
        return np.abs(np.linalg.eigvalsh(C)).sum()
    best = 1e9
    for r in range(int(sys.argv[2])):
        x0 = np.concatenate([rng.uniform(0, 2 * np.pi, len(E)), 0.05 * rng.standard_normal(len(E))])
        res = minimize(f, x0, method='Powell', options=dict(maxiter=200000, xtol=1e-8, ftol=1e-12))
        best = min(best, res.fun)
    print(f"m={m}: min ||C||_1 = {best:.5f}   sqrt3(m-1) = {np.sqrt(3)*(m-1):.5f}   ratio = {best/(np.sqrt(3)*(m-1)):.4f}   2(m-1) = {2*(m-1)}", flush=True)
