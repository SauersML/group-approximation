#!/usr/bin/env python3
"""Continuum (log-scale spread) limit of the size-law problem, heuristic.

With beta log-uniform (cdf u = B(k) = ln(k+1)/ln(N+1)) and alpha with cdf A(u), as N -> inf
    BC(alpha, beta)        -> int_0^1 sqrt(A'(u)) du
    BC(alpha*beta, beta)   -> int_0^1 sqrt(A(u) + u A'(u)) du
so J -> Phi[A] = 2 (int sqrt A')^2 + 2 int sqrt((uA)').  We maximise Phi over increasing
A: [0,1] -> [0,1], A(0) = 0, A(1) = 1, by discretising a = A' >= 0 on a midpoint grid.
"""
import numpy as np
from scipy.optimize import minimize

M = 300
u = (np.arange(M) + 0.5) / M
h = 1.0 / M


def phi_of(th):
    a = np.exp(th); a = a / (a.sum() * h)          # density of A, integrates to 1
    A = np.cumsum(a) * h - 0.5 * a * h             # A at midpoints
    t1 = np.sum(np.sqrt(a)) * h
    t2 = np.sum(np.sqrt(A + u * a)) * h
    return 2 * t1 * t1 + 2 * t2


def neg(th):
    return -phi_of(th)


if __name__ == "__main__":
    p = 0.87
    th0 = np.log(p * u ** (p - 1))
    print(f"u^p, p={p}: Phi/4 = {phi_of(th0)/4:.6f}")
    res = minimize(neg, th0, method="L-BFGS-B", options={"maxiter": 20000, "maxfun": 10**7})
    a = np.exp(res.x); a /= a.sum() * h
    print(f"optimised over A (M={M}): sup Phi/4 = {-res.fun/4:.6f}")
    for q in [0.01, 0.1, 0.3, 0.5, 0.7, 0.9, 0.99]:
        i = int(q * M)
        print(f"  u={q:.2f}  A'(u)={a[i]:.4f}   (u^0.87 would give {0.87*u[i]**(-0.13):.4f})")
