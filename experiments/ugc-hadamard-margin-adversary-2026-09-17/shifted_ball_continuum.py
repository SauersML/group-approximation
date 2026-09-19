"""Continuum cost of shifted-ball hand-off adversaries (exploratory, float).

Adversary S(f): i.i.d. radii rho_u (normalised by K) with density f on
[0, T], T < 1/2, shared by u and -u.  The owner of x is argmax of
V_u = rho_u - t_u(x) together with V_D = 0 for the dictator.  A(x) = v_u
if u owns x (v uniform signs, v_{-u} = -v_u); A(x) = tau x_i if D owns x.
Each codeword owns itself (rho < 1/2), so A is folded and random on P.

At a point x with competitor weights w_u = 1 - 2 t_u (Parseval:
sum w_u^2 <= 1), the worst edge at x costs at most
   sum_{u<u' moving oppositely along the edge} int_{z>=0} f(z+t_u) f(z+t_u') prod_{v!=u,u'} F(z+t_v) dz
 + (1/2) sum_u f(t_u) prod_{v!=u} F(t_v)
 + prod_v F(t_v).
Only competitors with t_u < T matter.  This script evaluates the bound on
profile families (N equal competitors; one plus N equal) and optimises a
piecewise-constant f by SLSQP on the epigraph.  Heuristic search only.
"""
import sys
import numpy as np
from scipy.optimize import minimize

M = 20
ZG = 200
PAIRS = "--equal-only" not in sys.argv


class Law:
    def __init__(self, p, T):
        self.p = np.asarray(p, float); self.T = T; self.h = T / len(p)
        self.cum = np.concatenate([[0], np.cumsum(self.p)])

    def F(self, s):
        s = np.asarray(s, float)
        b = np.clip((s / self.h).astype(int), 0, len(self.p) - 1)
        v = self.cum[b] + self.p[b] * (s - b * self.h) / self.h
        return np.where(s >= self.T, 1.0, np.where(s <= 0, 0.0, v))

    def f(self, s):
        s = np.asarray(s, float)
        b = np.clip((s / self.h).astype(int), 0, len(self.p) - 1)
        return np.where((s >= self.T) | (s < 0), 0.0, self.p[b] / self.h)


def cost_group(L, ts, ns):
    """competitor groups: ns[g] competitors at distance ts[g]."""
    ts = np.asarray(ts, float); ns = np.asarray(ns, int)
    F0 = L.F(ts); f0 = L.f(ts)
    D = np.prod(F0 ** ns)
    uD = 0.0
    for g in range(len(ts)):
        if ns[g] == 0:
            continue
        others = np.prod(F0 ** ns) / F0[g] if F0[g] > 0 else np.prod(np.delete(F0 ** ns, g)) * (0.0 if ns[g] > 1 else 1.0)
        uD += 0.5 * ns[g] * f0[g] * others
    tmin = ts.min()
    if tmin >= L.T:
        return D + uD
    z = np.linspace(0, L.T - tmin, ZG)
    Fz = np.array([L.F(z + t) for t in ts]); fz = np.array([L.f(z + t) for t in ts])
    # Only pairs moving in opposite directions along the edge can switch
    # ownership; maximise over the split of each group into the two sides.
    G = len(ts)

    def I(a, b, ex):
        return np.trapezoid(fz[a] * fz[b] * np.prod(Fz ** ex[:, None], axis=0), z)
    if G == 1:
        N = int(ns[0])
        if N < 2:
            return D + uD
        ex = ns.copy(); ex[0] -= 2
        return D + uD + (N * N // 4) * I(0, 0, ex)
    N2 = int(ns[1])
    ex12 = ns.copy(); ex12[0] -= 1; ex12[1] -= 1
    i12 = I(0, 1, ex12)
    i22 = 0.0
    if N2 >= 2:
        ex22 = ns.copy(); ex22[1] -= 2
        i22 = I(1, 1, ex22)
    return D + uD + max((N2 - m) * i12 + m * (N2 - m) * i22 for m in range(N2 + 1))


def profiles(T, dense=1, pairs=PAIRS):
    """t values on a grid of step T/(4 M dense) (bin interiors and both sides
    of every breakpoint), so the optimiser cannot hide mass between samples."""
    wmin = 1 - 2 * T
    out = []
    Nmax = int(np.floor(1 / wmin ** 2))
    eps = 1e-9
    base = np.arange(0, 4 * M * dense + 1) * T / (4 * M * dense)
    grid = np.unique(np.clip(np.concatenate([base, base - eps]), 0, T - eps))
    for N in range(1, Nmax + 1):
        tlo = (1 - 1 / np.sqrt(N)) / 2
        for t in grid[grid >= tlo - 1e-12]:
            out.append(([t], [N]))
    if not pairs:
        return out
    coarse = grid[:: 4 * dense]
    for t1 in coarse:
        rest = 1 - (1 - 2 * t1) ** 2
        for N2 in range(1, Nmax + 1):
            if N2 * wmin ** 2 > rest:
                break
            tlo = (1 - np.sqrt(rest / N2)) / 2
            for t2 in coarse[coarse >= tlo]:
                out.append(([t1, t2], [1, N2]))
    return out


def verify(p, T, dense=4):
    prof = profiles(T, dense)
    c = costs(p, T, prof)
    return c.max(), prof[int(c.argmax())], len(prof)


def costs(p, T, prof):
    L = Law(p, T)
    return np.array([cost_group(L, ts, ns) for ts, ns in prof])


def optimise(T, iters=200):
    prof = profiles(T)
    R0 = 1 / (1 - np.exp(-2 * T))
    mids = (np.arange(M) + 0.5) * T / M
    p0 = np.exp(-2 * mids); p0 /= p0.sum()
    x0 = np.concatenate([p0, [costs(p0, T, prof).max()]])
    cons = [{"type": "ineq", "fun": lambda x: x[-1] - costs(x[:-1], T, prof)},
            {"type": "eq", "fun": lambda x: x[:-1].sum() - 1}]
    res = minimize(lambda x: x[-1], x0, method="SLSQP", constraints=cons,
                   bounds=[(0, 1)] * M + [(0, None)], options={"maxiter": iters})
    p = np.clip(res.x[:-1], 0, None); p /= p.sum()
    c = costs(p, T, prof)
    return p, c.max(), prof[int(c.argmax())], R0, len(prof)


if __name__ == "__main__":
    for T in [float(a) for a in sys.argv[1:] if not a.startswith("-")] or [0.36, 0.40, 0.44]:
        p, val, arg, R0, n = optimise(T)
        print(f"T={T}: radial-only bound {R0:.4f}; optimised max cost {val:.4f} over {n} profiles; worst {arg}")
        print("  bin masses*M:", np.round(p * M, 2).tolist())
        vv, va, vn = verify(p, T)
        print(f"  dense re-check: max cost {vv:.4f} over {vn} profiles; worst {va}", flush=True)
