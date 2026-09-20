#!/usr/bin/env python3
"""The whole i.i.d. pointed-forest ansatz, reduced to two size laws.

For the n -> infinity Rayleigh quotient of the product-form vectors
    f(T_0..T_{m-1}; i) = Y(T_i) prod_{j != i} X(T_j)
(bulk weight X, pointer weight Y, any shapes, normalised sum_T X^2 = 1 = sum_T Y^2),
the reduction in thompson-f-iid-forest-vectors-cannot-reach-norm-one-proof gives
    4 R  <=  J(alpha, beta) = 2 BC(alpha, beta)^2 + 2 BC(alpha * beta, beta),
where alpha, beta are the size laws of X^2, Y^2, '*' is convolution and BC is the
Bhattacharyya coefficient, with equality attained by split-form shapes.  So
    sup (i.i.d. family, sizes <= N) = max { J/4 : alpha, beta on {1..N} }.

We parametrise a = sqrt(alpha), b = sqrt(beta) as unit vectors (a = exp(theta)/|.|) and
maximise with L-BFGS using an exact gradient.  Usage: size_law_problem.py N [N ...]
"""
import sys
import numpy as np
from scipy.optimize import minimize
from scipy.signal import fftconvolve


def conv(u, v):
    if len(u) * len(v) <= 4_000_000:
        return np.convolve(u, v)
    return np.maximum(fftconvolve(u, v), 0.0)


def corr(w, u):
    """c[k] = sum_s u[s] w[k+s] for arrays indexed by size 0..N (same length)."""
    L = len(w)
    full = conv(w[::-1], u)          # full[p] = sum_s w[L-1-(p-s)] u[s]
    # want index k+s = L-1-(p-s)  ->  p = L-1-k
    return full[L - 1 - np.arange(L)]


def J_and_grad(a, b):
    """a, b nonnegative unit vectors indexed by size 1..N (index 0 = size 1)."""
    N = len(a)
    A = np.concatenate([[0.0], a * a])         # indexed by size 0..N
    B = np.concatenate([[0.0], b * b])
    bb = np.concatenate([[0.0], b])
    ab = a @ b
    gam = conv(B, A)[: N + 1]                  # gam[j] = sum_{s+t=j} B_s A_t, sizes <= N
    G = np.sqrt(gam)
    t2 = bb @ G
    J = 2 * ab * ab + 2 * t2
    w = np.zeros(N + 1)
    nz = G > 0
    w[nz] = bb[nz] / G[nz]
    gb = G + bb * corr(w, A)                   # d t2 / d b_k
    ga = np.concatenate([[0.0], a]) * corr(w, B)  # d t2 / d a_t
    gJa = 4 * ab * b + 2 * ga[1:]
    gJb = 4 * ab * a + 2 * gb[1:]
    return J, gJa, gJb


def unpack(z, N):
    th, et = z[:N], z[N:]
    a = np.exp(th - th.max()); a /= np.linalg.norm(a)
    b = np.exp(et - et.max()); b /= np.linalg.norm(b)
    return a, b


def objective(z, N):
    a, b = unpack(z, N)
    J, ga, gb = J_and_grad(a, b)
    # chain rule through normalisation and exp
    ga_t = a * (ga - (ga @ a) * a)
    gb_t = b * (gb - (gb @ b) * b)
    return -J, -np.concatenate([ga_t, gb_t])


def optimise(N, z0=None, iters=20000):
    if z0 is None:
        k = np.arange(1, N + 1)
        z0 = np.concatenate([-0.5 * np.log(k) - 0.3 * k / N, -0.5 * np.log(k) - 0.1 * k / N])
    res = minimize(objective, z0, args=(N,), jac=True, method="L-BFGS-B",
                   options={"maxiter": iters, "maxfun": 3 * iters, "ftol": 1e-15, "gtol": 1e-11})
    return -res.fun / 4, res.x


def interp(z, Nold, Nnew):
    xs = np.log(np.arange(1, Nold + 1)); xn = np.log(np.arange(1, Nnew + 1))
    return np.concatenate([np.interp(xn, xs, z[:Nold], right=z[Nold - 1] - 5),
                           np.interp(xn, xs, z[Nold:], right=z[-1] - 5)])


if __name__ == "__main__":
    Ns = [int(v) for v in sys.argv[1:]] or [9, 20, 40, 80]
    z = None; Nprev = None
    for N in Ns:
        z0 = interp(z, Nprev, N) if z is not None else None
        r, z = optimise(N, z0)
        a, b = unpack(z, N)
        k = np.arange(1, N + 1)
        J, _, _ = J_and_grad(a, b)
        print(f"N={N:7d}  sup R = {r:.7f}   BC(a,b)={a@b:.5f}  alpha(1)={a[0]**2:.4f} beta(1)={b[0]**2:.4f}"
              f"  E_alpha|T|={np.sum(k*a*a):.2f}  E_beta|T|={np.sum(k*b*b):.2f}", flush=True)
        Nprev = N
        np.save(f"opt_N{N}.npy", z)
