#!/usr/bin/env python3
"""Scan a 3-parameter explicit family of size laws (scouting, floating point).

beta cdf  B(k) = ln((k+c)/(1+c)) / ln((N+c)/(1+c))   (shifted log-uniform), B(0) = 0
alpha cdf A(k) = B(k)^p
Usage: family_scan.py N
"""
import sys
import numpy as np
from scipy.optimize import minimize
from size_law_problem import J_and_grad


def laws(N, c, p):
    k = np.arange(0, N + 1, dtype=float)
    B = np.log((k + c) / c) / np.log((N + c) / c)
    beta = np.diff(B)
    alpha = np.diff(B ** p)
    return np.sqrt(alpha), np.sqrt(beta)


def R(N, c, p):
    a, b = laws(N, c, p)
    return J_and_grad(a, b)[0] / 4


if __name__ == "__main__":
    N = int(sys.argv[1])
    best = None
    for c in [1.0, 2.0, 4.0, 8.0, 16.0]:
        for p in [0.8, 0.87, 0.95]:
            r = R(N, c, p)
            if best is None or r > best[0]:
                best = (r, c, p)
    res = minimize(lambda z: -R(N, np.exp(z[0]), z[1]), [np.log(best[1]), best[2]],
                   method="Nelder-Mead", options={"xatol": 1e-4, "fatol": 1e-9})
    print(f"N={N}  grid best {best}   refined: c={np.exp(res.x[0]):.4f} p={res.x[1]:.4f}  R={-res.fun:.6f}",
          flush=True)
