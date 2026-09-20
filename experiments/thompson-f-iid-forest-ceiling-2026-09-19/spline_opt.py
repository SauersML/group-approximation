#!/usr/bin/env python3
"""Optimise J/4 over size laws with a low-dimensional log-scale parametrisation (floating point).

log alpha_k = sum_i ca_i h_i(x_k) + const, log beta_k = sum_i cb_i h_i(x_k) + const, where
x_k = ln k / ln N in [0, 1] and h_i are piecewise-linear hat functions on K equally spaced knots.
The objective and gradient are the exact ones of size_law_problem (chain rule through the basis).
Usage: spline_opt.py K N1 N2 ...   (warm start carries the knot coefficients from N to N).
Saves spline_K{K}_N{N}.npy = coefficient vector.
"""
import sys
import numpy as np
from scipy.optimize import minimize
from scipy.sparse import csr_matrix
from size_law_problem import J_and_grad


def basis(N, K):
    x = np.log(np.arange(1, N + 1)) / np.log(N) * (K - 1)
    i = np.minimum(np.floor(x).astype(int), K - 2)
    f = x - i
    rows = np.concatenate([np.arange(N), np.arange(N)])
    cols = np.concatenate([i, i + 1])
    vals = np.concatenate([1 - f, f])
    return csr_matrix((vals, (rows, cols)), shape=(N, K))


def laws_from(z, H):
    K = H.shape[1]
    la = H @ z[:K] - 0.5 * np.log(np.arange(1, H.shape[0] + 1))
    lb = H @ z[K:] - 0.5 * np.log(np.arange(1, H.shape[0] + 1))
    a = np.exp(la - la.max()); a /= np.linalg.norm(a)
    b = np.exp(lb - lb.max()); b /= np.linalg.norm(b)
    return a, b


def objective(z, H):
    K = H.shape[1]
    a, b = laws_from(z, H)
    J, ga, gb = J_and_grad(a, b)
    ga_t = a * (ga - (ga @ a) * a)
    gb_t = b * (gb - (gb @ b) * b)
    return -J, -np.concatenate([H.T @ ga_t, H.T @ gb_t])


if __name__ == "__main__":
    K = int(sys.argv[1])
    Ns = [int(v) for v in sys.argv[2:]]
    z = np.zeros(2 * K)
    for N in Ns:
        H = basis(N, K)
        res = minimize(objective, z, args=(H,), jac=True, method="L-BFGS-B",
                       options={"maxiter": 5000, "ftol": 1e-14, "gtol": 1e-10})
        z = res.x
        a, b = laws_from(z, H)
        print(f"K={K} N={N:9d}  R = {-res.fun/4:.7f}  alpha(1)={a[0]**2:.4f} beta(1)={b[0]**2:.4f}"
              f"  iters={res.nit}", flush=True)
        np.save(f"spline_K{K}_N{N}.npy", z)
