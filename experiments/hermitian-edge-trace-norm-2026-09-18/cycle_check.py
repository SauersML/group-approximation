"""Check the odd-cycle theorem: for odd n, min ||C||_1 over Hermitian C supported on the
edges of C_n with |C_e| >= 1 equals 2 cot(pi/(2n)).
(a) scan the flux Phi for unit moduli; (b) random admissible C (random moduli >= 1, phases)
never go below the bound; (c) local minimization from random starts (L-BFGS-B) lands on it."""
import numpy as np
from scipy.optimize import minimize
rng = np.random.default_rng(1)

def cyc(c, th):
    n = len(c); C = np.zeros((n, n), complex)
    for j in range(n):
        C[j, (j+1) % n] = c[j]*np.exp(1j*th[j]); C[(j+1) % n, j] = np.conj(C[j, (j+1) % n])
    return C

tn = lambda C: np.abs(np.linalg.eigvalsh(C)).sum()
for n in [3, 5, 7, 9, 11, 13]:
    bound = 2/np.tan(np.pi/(2*n))
    scan = min(tn(cyc(np.ones(n), np.full(n, P/n))) for P in np.linspace(0, 2*np.pi, 4001))
    rnd = min(tn(cyc(1+rng.exponential(0.3, n), rng.uniform(0, 2*np.pi, n))) for _ in range(20000))
    def f(x):
        return tn(cyc(1+x[:n]**2, x[n:]))
    loc = min(minimize(f, rng.normal(size=2*n), method='L-BFGS-B').fun for _ in range(20))
    print(f"n={n:2d} 2cot(pi/2n)={bound:.6f} flux-scan={scan:.6f} random-min={rnd:.6f} "
          f"local-min={loc:.6f} need sqrt3(n+1)/2={np.sqrt(3)*(n+1)/2:.4f}")
