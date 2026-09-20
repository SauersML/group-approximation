#!/usr/bin/env python3
"""Spread-limit check: explicit log-uniform size laws, no optimisation.

beta has cdf B(k) = ln(k+1)/ln(N+1) on {1..N}; alpha has cdf B(k)^p.
The continuum heuristic predicts J/4 -> Phi(p)/4 with
Phi = 2 (int sqrt(A'))^2 + 2 int sqrt((uA)'), A(u) = u^p,
i.e. Phi(p) = 2 (2 sqrt p/(p+1))^2 + 2 * 2 sqrt(p+1)/(p+2)   (max ~ 3.896 at p ~ 0.87).
"""
import numpy as np
from size_law_problem import J_and_grad


def laws(N, p):
    k = np.arange(1, N + 1, dtype=float)
    B = np.log(k + 1) / np.log(N + 1)
    B0 = np.concatenate([[0.0], B])
    beta = np.diff(B0)
    alpha = np.diff(B0 ** p)
    return np.sqrt(alpha), np.sqrt(beta)


def phi(p):
    return 2 * (2 * np.sqrt(p) / (p + 1)) ** 2 + 2 * 2 * np.sqrt(p + 1) / (p + 2)


if __name__ == "__main__":
    ps = [0.8, 0.87, 1.0]
    print("continuum Phi/4:", "  ".join(f"p={p}: {phi(p)/4:.5f}" for p in ps))
    for N in [10**3, 10**4, 10**5, 10**6]:
        row = []
        for p in ps:
            a, b = laws(N, p)
            J = J_and_grad(a, b)[0]
            row.append(f"p={p}: {J/4:.5f}")
        print(f"N={N:8d}  " + "  ".join(row), flush=True)
