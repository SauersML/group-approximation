#!/usr/bin/env python3
"""Numerical sanity checks for low-label-threshold-rank-reductions-cannot-prove-ugc.

Checks, on random planted unique games (weighted multigraphs, arbitrary
permutation constraints, adversarial-ish corruption of an eps fraction of edges):

  (L1) the label-extended walk A_L is self-adjoint in L2(pi_L) and stochastic;
  (L2) <f, A_L f>_pi_L = val(x) for the labeling indicator f;
  (L3) ||f_lo||^2 <= (1 - val(x)) / (1 - theta) for the spectral split at theta;
  (L4) rounding any g by per-vertex argmax fails on a set S with
       pi(S) <= 2 ||g - f||^2, and val(x_g) >= val(x) - 2 pi(S);
  (L5) twisted trace: Tr(A_L^(2t)) <= k Tr(A^(2t)), hence
       rank_theta(A_L) <= k Tr(A^(2t)) / theta^(2t);
  (L6) end-to-end grid enumeration over the top eigenspace (small r) returns a
       labeling of value >= 1 - eps - 4 (eta + sqrt(2/C))^2 on YES instances.

Run: python3 check_label_rank_kill.py   (exits nonzero on any failure)
"""
import itertools
import math
import sys

import numpy as np

rng = np.random.default_rng(20260917)
FAIL = []


def check(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + (" " + detail if detail else ""))
    if not ok:
        FAIL.append(name)


def random_instance(n, k, deg, eps, planted=True):
    """Edge list (u, v, w, sigma) with sigma a permutation array: label a at u
    is consistent with label sigma[a] at v."""
    x = rng.integers(0, k, size=n)
    edges = []
    for _ in range(deg):
        perm = rng.permutation(n)
        for i in range(0, n - 1, 2):
            u, v = int(perm[i]), int(perm[i + 1])
            w = float(rng.uniform(0.5, 1.5))
            sigma = rng.permutation(k)
            if planted:
                # force sigma[x_u] = x_v
                j = int(np.where(sigma == x[v])[0][0])
                sigma[j], sigma[x[u]] = sigma[x[u]], sigma[j]
            edges.append([u, v, w, sigma])
    if planted:
        m = len(edges)
        for idx in rng.choice(m, size=int(round(eps * m)), replace=False):
            u, v, w, sigma = edges[idx]
            # corrupt: make x_u map to a wrong label
            b = (x[v] + 1 + rng.integers(0, k - 1)) % k
            j = int(np.where(sigma == b)[0][0])
            sigma[j], sigma[x[u]] = sigma[x[u]], sigma[j]
    return x, edges


def matrices(n, k, edges):
    W = np.zeros((n, n))
    WL = np.zeros((n * k, n * k))
    for u, v, w, sigma in edges:
        W[u, v] += w
        W[v, u] += w
        inv = np.argsort(sigma)
        for a in range(k):
            WL[u * k + a, v * k + sigma[a]] += w
            WL[v * k + a, u * k + inv[a]] += w
    deg = W.sum(axis=1)
    Wtot = sum(e[2] for e in edges)
    pi = deg / (2 * Wtot)
    A = W / deg[:, None]
    AL = WL / np.repeat(deg, k)[:, None]
    return A, AL, pi, Wtot


def value(x, edges, Wtot):
    return sum(w for u, v, w, s in edges if s[x[u]] == x[v]) / Wtot


def spectral(AL, pi, k):
    piL = np.repeat(pi, k)
    s = np.sqrt(piL)
    B = (s[:, None] * AL) / s[None, :]  # symmetric similar matrix
    B = (B + B.T) / 2
    lam, U = np.linalg.eigh(B)
    Phi = U / s[:, None]  # columns orthonormal in L2(pi_L)
    return lam, Phi, piL


def inner(f, g, piL):
    return float(np.sum(piL * f * g))


def round_labels(g, n, k):
    return np.argmax(g.reshape(n, k), axis=1)


def run_structural(n, k, deg, eps, C):
    x, edges = random_instance(n, k, deg, eps)
    A, AL, pi, Wtot = matrices(n, k, edges)
    lam, Phi, piL = spectral(AL, pi, k)
    check("L1 stochastic", np.allclose(AL.sum(axis=1), 1.0))
    M = piL[:, None] * AL
    check("L1 self-adjoint", np.allclose(M, M.T))
    f = np.zeros(n * k)
    f[np.arange(n) * k + x] = 1.0
    val = value(x, edges, Wtot)
    check("L2 rayleigh = val", abs(inner(f, AL @ f, piL) - val) < 1e-10,
          "val=%.4f" % val)
    theta = 1 - C * (1 - val) if C * (1 - val) < 1 else 0.0
    coeff = Phi.T @ (piL * f)
    hi = lam >= theta
    f_hi = Phi[:, hi] @ coeff[hi]
    f_lo = f - f_hi
    lo2 = inner(f_lo, f_lo, piL)
    check("L3 low mass", lo2 <= (1 - val) / (1 - theta) + 1e-9,
          "||f_lo||^2=%.4f bound=%.4f r=%d" % (lo2, (1 - val) / (1 - theta), hi.sum()))
    for noise in [0.0, 0.5, 1.5, 3.0]:
        g = f_hi + noise * rng.standard_normal(n * k) / math.sqrt(k)
        xg = round_labels(g, n, k)
        S = xg != x
        dist2 = inner(g - f, g - f, piL)
        check("L4 failing mass (noise %.1f)" % noise, pi[S].sum() <= 2 * dist2 + 1e-9,
              "pi(S)=%.4f 2||g-f||^2=%.4f" % (pi[S].sum(), 2 * dist2))
        check("L4 value loss (noise %.1f)" % noise,
              value(xg, edges, Wtot) >= val - 2 * pi[S].sum() - 1e-9)
    for t in [1, 2, 5, 10]:
        trL = np.trace(np.linalg.matrix_power(AL, 2 * t))
        trG = np.trace(np.linalg.matrix_power(A, 2 * t))
        check("L5 twisted trace t=%d" % t, trL <= k * trG + 1e-8,
              "Tr L=%.3f k Tr A=%.3f" % (trL, k * trG))
        th = 0.9
        rank = int((lam >= th).sum())
        check("L5 rank bound t=%d" % t, rank <= k * trG / th ** (2 * t) + 1e-8)


def run_enumeration(n, k, deg, eps, C, eta):
    """Planted instance on an expander-like multigraph: top eigenspace of A_L at
    1 - (C+1) eps has dimension about k (the k gauge copies)."""
    x, edges = random_instance(n, k, deg, eps)
    A, AL, pi, Wtot = matrices(n, k, edges)
    lam, Phi, piL = spectral(AL, pi, k)
    val = value(x, edges, Wtot)
    theta = 1 - (C + 1) * eps
    hi = np.where(lam >= theta)[0]
    r = len(hi)
    step = 2 * eta / math.sqrt(r)
    levels = np.arange(-1 - eta, 1 + eta + 1e-12, step)
    best = 0.0
    count = 0
    for c in itertools.product(levels, repeat=r):
        c = np.array(c)
        if np.sum(c ** 2) > (1 + eta) ** 2:
            continue
        count += 1
        g = Phi[:, hi] @ c
        best = max(best, value(round_labels(g, n, k), edges, Wtot))
    bound = 1 - eps - 4 * (eta + math.sqrt(2.0 / C)) ** 2
    check("L6 enumeration r=%d grid=%d" % (r, count), best >= bound,
          "val(planted)=%.4f best=%.4f bound=%.4f" % (val, best, bound))


def run_greedy(n, k, deg, eps, gamma, tau, eta):
    """(L7) The eigen-free algorithm of the route: P = B^t with B = (I + A_L)/2,
    greedy pi_L-Gram-Schmidt column selection until every column residual^2 <=
    tau, then grid over the selected span. Checks m <= 2R (R = #lambda_B >=
    1 - gamma), the leakage chain, and the end-to-end value bound with the
    measured leakage delta (floats, so tau is moderate here)."""
    x, edges = random_instance(n, k, deg, eps)
    A, AL, pi, Wtot = matrices(n, k, edges)
    piL = np.repeat(pi, k)
    nL = n * k
    val = value(x, edges, Wtot)
    B = (np.eye(nL) + AL) / 2
    t = int(math.ceil(math.log(nL / tau) / gamma))
    P = np.linalg.matrix_power(B, t)
    lamB, Phi, _ = spectral(B, pi, k)
    R = int((lamB >= 1 - gamma).sum())
    basis = []
    while True:
        res = P.copy()
        for v in basis:
            coef = (piL * v) @ P / inner(v, v, piL)
            res = res - np.outer(v, coef)
        norms = (piL[:, None] * res ** 2).sum(axis=0)
        j = int(np.argmax(norms))
        if norms[j] <= tau:
            break
        basis.append(res[:, j].copy())
    m = len(basis)
    check("L7 greedy stops at m <= 2R", m <= max(2 * R, 0),
          "m=%d R=%d t=%d" % (m, R, t))
    f = np.zeros(nL)
    f[np.arange(n) * k + x] = 1.0
    theta_hi = 1 - gamma / 8
    coeff = Phi.T @ (piL * f)
    hi = lamB >= theta_hi
    f_hi = Phi[:, hi] @ coeff[hi]
    lo2 = inner(f - f_hi, f - f_hi, piL)
    check("L7 low mass", lo2 <= (1 - inner(f, B @ f, piL)) / (gamma / 8) + 1e-9,
          "||f_lo||^2=%.4f" % lo2)

    def proj(h):
        out = np.zeros(nL)
        for v in basis:
            out += inner(h, v, piL) / inner(v, v, piL) * v
        return out

    delta = math.sqrt(max(inner(f_hi - proj(f_hi), f_hi - proj(f_hi), piL), 0.0))
    psi = []
    for v in basis:
        e = int(math.floor(0.5 * math.log2(inner(v, v, piL))))
        psi.append(v / 2.0 ** e)
    h = eta / math.sqrt(max(m, 1))
    levels = np.arange(-1.0, 1.0 + h, h)
    best = 0.0
    for c in itertools.product(levels, repeat=m):
        g = sum((ci * p for ci, p in zip(c, psi)), np.zeros(nL))
        best = max(best, value(round_labels(g, n, k), edges, Wtot))
    bound = val - 4 * (eta + delta + math.sqrt(lo2)) ** 2
    check("L7 greedy grid value", best >= bound,
          "best=%.4f bound=%.4f delta=%.2e grid=%d" % (best, bound, delta,
                                                      len(levels) ** m))


if __name__ == "__main__":
    run_greedy(n=40, k=2, deg=8, eps=0.005, gamma=0.5, tau=1e-7, eta=0.25)
    run_greedy(n=30, k=3, deg=8, eps=0.0, gamma=0.6, tau=1e-7, eta=0.3)
    run_structural(n=40, k=4, deg=6, eps=0.02, C=10)
    run_structural(n=30, k=5, deg=4, eps=0.05, C=5)
    run_enumeration(n=60, k=2, deg=8, eps=0.004, C=40, eta=0.1)
    run_enumeration(n=40, k=3, deg=8, eps=0.003, C=40, eta=0.12)
    if FAIL:
        print("FAILED:", FAIL)
        sys.exit(1)
    print("ALL CHECKS PASSED")
