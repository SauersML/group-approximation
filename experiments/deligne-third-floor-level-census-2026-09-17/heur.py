"""Upper bounds for mu_theta(X): smooth local search on phases + LP polishing with rounded integers.

Every reported value is re-evaluated by defect.defect_of on the returned phases, so it is a
certified upper bound (a monomial model with that uniform defect exists).
"""
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog, minimize
from defect import build, defect_of
from presentation import RELATORS


class Problem:
    def __init__(self, perm, theta, relators=RELATORS):
        cost, A, lo, hi, lb, ub, integ, nva = build(perm, theta, relators)
        self.perm, self.theta, self.rel = perm, theta, relators
        self.nva = nva
        ncell = int(integ.sum())
        # rows come in pairs (upper, lower) per cell; extract holonomy matrix H (cells x a)
        A = A.tocsr()
        H = A[0::2, :nva]
        self.H = sp.csr_matrix(H)
        self.tk = np.array(lo[1::2])  # theta*k per cell (lower rows have lo = theta k)
        self.fixed = np.zeros(nva, dtype=bool)  # no gauge fixing (lets us start from pulled-back models)
        self.ncell = ncell

    def resid(self, a):
        d = self.H @ a - self.tk
        return d - np.rint(d)

    def smooth_opt(self, a0, p=8, iters=400):
        free = ~self.fixed
        H = self.H[:, free]

        def f(z):
            a = np.zeros(self.nva); a[free] = z
            d = self.H @ a - self.tk
            s = np.sin(np.pi * d)
            val = np.sum(s ** (2 * p))
            g = H.T @ ((2 * p) * s ** (2 * p - 1) * np.cos(np.pi * d) * np.pi)
            return val, g
        r = minimize(f, a0[free], jac=True, method="L-BFGS-B", options={"maxiter": iters})
        a = np.zeros(self.nva); a[free] = r.x
        return a

    def lp_polish(self, a):
        """Fix n = round(H a - tk), solve min t s.t. |H a - tk - n| <= t exactly."""
        free = np.where(~self.fixed)[0]
        H = self.H[:, free]
        n = np.rint(self.H @ a - self.tk)
        m = H.shape[0]
        nv = len(free) + 1
        ones = sp.csr_matrix(np.ones((m, 1)))
        Aub = sp.vstack([sp.hstack([H, -ones]), sp.hstack([-H, -ones])]).tocsc()
        bub = np.concatenate([self.tk + n, -(self.tk + n)])
        c = np.zeros(nv); c[-1] = 1
        bounds = [(None, None)] * len(free) + [(0, None)]
        r = linprog(c, A_ub=Aub, b_ub=bub, bounds=bounds, method="highs")
        a2 = np.zeros(self.nva); a2[free] = r.x[:-1]
        return a2, r.x[-1]

    def search(self, starts=20, seed=0, init=None):
        rng = np.random.default_rng(seed)
        best, best_a = 1.0, None
        for s in range(starts):
            if init is not None and s == 0:
                a0 = init.copy()
            else:
                a0 = rng.random(self.nva)
            a0[self.fixed] = 0
            a = a0
            for p in (1, 2, 4, 8, 16):
                a = self.smooth_opt(a, p=p)
            prev = 2.0
            for _ in range(30):
                a, t = self.lp_polish(a)
                if t >= prev - 1e-12:
                    break
                prev = t
            val = defect_of(self.perm, self.theta, a, self.rel)
            if val < best - 1e-12:
                best, best_a = val, a
        return best, best_a
