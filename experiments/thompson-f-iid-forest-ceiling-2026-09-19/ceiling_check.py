#!/usr/bin/env python3
"""Sanity check of the ceiling chain (floating point; the proof is analytic).

For each pair of laws it prints
    4 - J  >=  2 (H1^2 + H2^2)  >=  1/20,
with H1^2 = 1 - BC(alpha, beta), H2^2 = 1 - BC(alpha*beta, beta) (untruncated), and the Laplace
step t1 + 2 t2 >= 1/2 (TV distances) at the lambda where psi_beta(lambda) = 1/2.
Laws: the optimisers opt_N*.npy, spline_K24_N*.npy, and random laws.
"""
import glob
import numpy as np
from scipy.optimize import brentq
from size_law_problem import J_and_grad, unpack


def check(al, be, name):
    N = len(al)
    k = np.arange(1, N + 1)
    c = np.convolve(be, al)            # sizes 2..2N
    ck = np.arange(2, 2 * N + 1)
    J = J_and_grad(np.sqrt(al), np.sqrt(be))[0]
    bc1 = np.sum(np.sqrt(al * be))
    bef = np.zeros(2 * N); bef[:N] = be          # sizes 1..2N
    cf = np.zeros(2 * N); cf[1:] = c
    bc2 = np.sum(np.sqrt(bef * cf))
    H1, H2 = 1 - bc1, 1 - bc2
    t1 = 0.5 * np.abs(al - be).sum()
    t2 = 0.5 * np.abs(cf - bef).sum()
    lam = brentq(lambda l: np.sum(be * np.exp(-l * k)) - 0.5, 1e-12, 50.0)
    ok = (4 - J >= 2 * (H1 + H2) - 1e-12) and (2 * (H1 + H2) >= 0.05) and (t1 + 2 * t2 >= 0.5 - 1e-12)
    print(f"{name:26s} J/4={J/4:.6f}  4-J={4-J:.5f}  2(H1^2+H2^2)={2*(H1+H2):.5f}  t1+2t2={t1+2*t2:.4f}"
          f"  lambda={lam:.3g}  {'OK' if ok else 'FAIL'}")
    return ok


allok = True
for f in sorted(glob.glob("opt_N*.npy"), key=lambda s: int(s[5:-4])):
    N = int(f[5:-4]); a, b = unpack(np.load(f), N)
    allok &= check(a * a, b * b, f)
try:
    from spline_opt import basis, laws_from
    for f in sorted(glob.glob("spline_K24_N*.npy"), key=lambda s: int(s[12:-4])):
        N = int(f[12:-4])
        if N > 20000:          # np.convolve is O(N^2); larger N skipped
            continue
        a, b = laws_from(np.load(f), basis(N, 24))
        allok &= check(a * a, b * b, f)
except ImportError:
    pass
rng = np.random.default_rng(1)
for i in range(5):
    N = int(rng.integers(3, 300))
    al = rng.random(N) ** 3; al /= al.sum()
    be = rng.random(N) ** 3; be /= be.sum()
    allok &= check(al, be, f"random N={N}")
print("ALL OK" if allok else "SOME FAIL")
