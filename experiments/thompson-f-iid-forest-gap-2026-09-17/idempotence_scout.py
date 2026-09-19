#!/usr/bin/env python3
"""Floating-point scouting (not a certificate): how small can Hellinger(nu, nu*nu) be for a
probability law nu on {1..M}?  The gap theorem only uses the rigorous bound >= 1/8
(sup_t |phi - phi^2| >= 1/4).  Here we minimise H^2 = 2 - 2 sum_k sqrt(nu_k (nu*nu)_k) over
softmax-parametrised nu with L-BFGS, for growing M, and compare with the log-uniform family
nu_s ~ 1/s on [1, M] (whose limit value is H^2 = 2 - 4 sqrt(2)/3 = 0.1144).
Usage: python3 idempotence_scout.py [M ...]    (default 50 200 800; about a minute)
"""
import sys
import numpy as np
from scipy.optimize import minimize


def H2_and_grad(theta):
    w = np.exp(theta - theta.max())
    nu = w / w.sum()                       # nu[i] is the mass of size i+1
    c = np.convolve(nu, nu)                # c[k] is the mass of size k+2
    M = len(nu)
    # align on sizes 1..2M: nu at sizes 1..M, c at sizes 2..2M
    nuf = np.concatenate([nu, np.zeros(M)])
    cf = np.concatenate([[0.0], c])
    prod = np.sqrt(nuf * cf)
    A = prod.sum()
    with np.errstate(divide='ignore', invalid='ignore'):
        r1 = np.where(nuf > 0, np.sqrt(cf / np.maximum(nuf, 1e-300)), 0.0) / 2   # dA/dnu (direct)
        r2 = np.where(cf > 0, np.sqrt(nuf / np.maximum(cf, 1e-300)), 0.0) / 2    # dA/dc
    # dA/dnu_j = r1[j] + sum_k r2[k] * 2 * nu[k - j - 1] (size bookkeeping)
    g_nu = r1[:M].copy()
    r2c = r2[1:]                           # r2 at sizes 2..2M, index k -> size k+2
    g_nu += 2 * np.correlate(r2c, nu, mode='full')[M - 1:2 * M - 1][:M]
    # softmax chain rule
    g_theta = nu * (g_nu - (nu * g_nu).sum())
    return 2 - 2 * A, 2 * g_theta * -1


def loguniform(M):
    s = np.arange(1, M + 1, dtype=float)
    nu = 1 / s
    return np.log(nu)


if __name__ == '__main__':
    Ms = [int(a) for a in sys.argv[1:]] or [50, 200, 800]
    for M in Ms:
        th0 = loguniform(M)
        h_lu = H2_and_grad(th0)[0]
        res = minimize(H2_and_grad, th0, jac=True, method='L-BFGS-B', options={'maxiter': 5000})
        print(f"M={M}: log-uniform H^2={h_lu:.5f} (H={np.sqrt(h_lu):.4f});  "
              f"minimised H^2={res.fun:.5f} (H={np.sqrt(max(res.fun, 0)):.4f})")
