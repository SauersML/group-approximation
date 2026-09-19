#!/usr/bin/env python3
"""Numerical check of the XOR Cheeger inequality (xor-cheeger-sdp-deficit-at-least-sqrt-gap-times-frustration).

Setting: a signed graph (V, E, w, sigma) with edge law P(u,v) = w_uv / W (both orientations),
stationary vertex law pi(u) = deg_w(u) / (2W), normalized-Laplacian gap lam = lambda_2(I - D^-1 A).
XOR SDP deficit of unit vectors x_u:  delta(x) = E_e |x_u - sigma_e x_v|^2 / 4.
gamma = 1 - val = min over +-1 labellings of the violated edge mass.

The theorem: for EVERY unit-vector solution x (not only an optimum),
    gamma <= E[violations of the rounding R(x)] <= 27 * delta(x) / sqrt(lam).
We check, on many instances:
  (a) tau := 1 - lambda_max(E_pi x x^T) <= 4 delta / lam                     (Step 1)
  (b) twisted energy of g = <x, w>:  E_e (g_u - sigma g_v)^2 <= 4 delta       (Step 2)
  (c) the exact expectation (over theta, and Monte Carlo over zeta) of the
      violations of the rounding R is <= 26.7 * delta / sqrt(lam)           (Steps 3-5)
  (d) with exact gamma (brute force, small n) the ratio delta_BM/(sqrt(lam) gamma),
      where delta_BM is a Burer-Monteiro local optimum (an UPPER bound on delta_sdp).
Only (a)-(c) are proof checks; (d) is a tightness indication (domain walls give a constant).
"""
import itertools
import math
import sys

import numpy as np

RNG = np.random.default_rng(20260919)
CONST = 26.7


def lap_gap(n, edges):
    A = np.zeros((n, n))
    for (u, v, w, s) in edges:
        A[u, v] += w
        A[v, u] += w
    d = A.sum(1)
    Dm = np.diag(1 / np.sqrt(d))
    L = np.eye(n) - Dm @ A @ Dm
    ev = np.sort(np.linalg.eigvalsh(L))
    return ev[1], d


def edge_arrays(edges):
    U = np.array([e[0] for e in edges])
    V = np.array([e[1] for e in edges])
    Wt = np.array([e[2] for e in edges], float)
    S = np.array([e[3] for e in edges], float)
    return U, V, Wt / Wt.sum(), S


def deficit(X, U, V, P, S):
    D = X[U] - S[:, None] * X[V]
    return float(np.sum(P * np.sum(D * D, 1)) / 4)


def burer_monteiro(n, U, V, P, S, r=None, iters=3000, restarts=3):
    r = r or max(3, int(math.ceil(math.sqrt(2 * n))) + 1)
    best = None
    for _ in range(restarts):
        X = RNG.standard_normal((n, r))
        X /= np.linalg.norm(X, axis=1, keepdims=True)
        step = 0.5
        for it in range(iters):
            G = np.zeros_like(X)
            c = (P * S)[:, None]
            np.add.at(G, U, c * X[V])
            np.add.at(G, V, c * X[U])
            # Riemannian ascent on sphere product; scale by vertex mass
            X = X + step * G / (np.abs(G).max() + 1e-12)
            X /= np.linalg.norm(X, axis=1, keepdims=True)
            if it % 500 == 499:
                step *= 0.6
        dval = deficit(X, U, V, P, S)
        if best is None or dval < best[0]:
            best = (dval, X)
    return best


def exact_gamma(n, U, V, P, S):
    best = 1.0
    if n > 20:
        return None
    for bits in range(1 << (n - 1)):
        x = np.array([1 - 2 * ((bits >> i) & 1) for i in range(n)], float)
        viol = float(np.sum(P * (x[U] != S * x[V])))
        best = min(best, viol)
    return best


def rounding_expectation(X, U, V, P, S, pi, s=0.5, zeta_samples=200):
    """Exact expectation over theta ~ U(0,1); Monte Carlo over the Gaussian zeta."""
    M = (X * pi[:, None]).T @ X
    evals, evecs = np.linalg.eigh(M)
    wv = evecs[:, -1]
    tau = 1 - evals[-1]
    g = X @ wv
    en = float(np.sum(P * (g[U] - S * g[V]) ** 2))
    y = np.clip(g / s, -1, 1)
    a = np.abs(y)
    au, av = a[U], a[V]
    same = np.sign(y[U]) == np.sign(S * y[V])
    lo, hi = np.minimum(au, av), np.maximum(au, av)
    # P_theta[exactly one determined or both determined and violated]
    p_bad = np.where(same, hi - lo, hi)
    # both undetermined: theta >= hi  (prob 1 - hi), then hyperplane fill
    p_both_und = 1 - hi
    c = np.sum(X[U] * (S[:, None] * X[V]), 1)
    p_hyp = np.arccos(np.clip(c, -1, 1)) / math.pi  # exact over zeta
    exp_viol = float(np.sum(P * (p_bad + p_both_und * p_hyp)))
    return tau, en, exp_viol


def check(name, n, edges, results):
    lam, d = lap_gap(n, edges)
    U, V, P, S = edge_arrays(edges)
    pi = d / d.sum()
    dl, X = burer_monteiro(n, U, V, P, S)
    tau, en, ev = rounding_expectation(X, U, V, P, S, pi)
    gam = exact_gamma(n, U, V, P, S)
    okA = tau <= 4 * dl / lam + 1e-9
    okB = en <= 4 * dl + 1e-9
    okC = ev <= CONST * dl / math.sqrt(lam) + 1e-9
    okG = gam is None or gam <= ev + 1e-9
    ratio = (dl / (math.sqrt(lam) * gam)) if gam else float('nan')
    results.append(okA and okB and okC and okG)
    print(f"{name:28s} n={n:4d} lam={lam:.4f} delta={dl:.5f} tau={tau:.4f}<= {4*dl/lam:.4f} "
          f"E[viol]={ev:.4f} <= {CONST*dl/math.sqrt(lam):.4f} gamma={gam if gam is None else round(gam,5)} "
          f"delta/(sqrt(lam)gamma)={ratio:.3f} {'OK' if results[-1] else 'FAIL'}")


def cycle_wall(m):
    return [(i, (i + 1) % m, 1.0, -1.0 if i == 0 else 1.0) for i in range(m)]


def torus_wall(a, b):
    E = []
    idx = lambda i, j: (i % a) * b + (j % b)
    for i in range(a):
        for j in range(b):
            E.append((idx(i, j), idx(i + 1, j), 1.0, -1.0 if i == a - 1 else 1.0))
            E.append((idx(i, j), idx(i, j + 1), 1.0, 1.0))
    return E


def random_regular_signed(n, d, p_neg):
    while True:
        stubs = np.repeat(np.arange(n), d)
        RNG.shuffle(stubs)
        pairs = stubs.reshape(-1, 2)
        if np.all(pairs[:, 0] != pairs[:, 1]):
            break
    return [(int(u), int(v), 1.0, -1.0 if RNG.random() < p_neg else 1.0) for u, v in pairs]


def hypercube_flux(k):
    n = 1 << k
    E = []
    for x in range(n):
        for i in range(k):
            y = x ^ (1 << i)
            if x < y:
                s = -1.0 if (i == 0 and (x >> 1) & 1) else 1.0
                E.append((x, y, 1.0, s))
    return E


def ladder_wall(m, rungs_w):
    # two cycles joined by rungs; wall on both cycles at edge 0
    E = []
    for i in range(m):
        E.append((i, (i + 1) % m, 1.0, -1.0 if i == 0 else 1.0))
        E.append((m + i, m + (i + 1) % m, 1.0, -1.0 if i == 0 else 1.0))
        E.append((i, m + i, rungs_w, 1.0))
    return E


def main():
    results = []
    for m in [6, 10, 14, 18]:
        check(f"cycle-wall m={m}", m, cycle_wall(m), results)
    for (a, b) in [(4, 4), (6, 3), (4, 5)]:
        check(f"torus-wall {a}x{b}", a * b, torus_wall(a, b), results)
    for (m, w) in [(8, 0.2), (9, 3.0)]:
        check(f"ladder-wall m={m} w={w}", 2 * m, ladder_wall(m, w), results)
    for k in [3, 4]:
        check(f"hypercube-flux k={k}", 1 << k, hypercube_flux(k), results)
    for (n, d, p) in [(16, 3, 0.1), (18, 4, 0.05), (20, 3, 0.5), (16, 6, 0.02)]:
        check(f"rand-reg n={n} d={d} p={p}", n, random_regular_signed(n, d, p), results)
    # larger instances: proof checks (a)-(c) only
    for m in [60, 200]:
        check(f"cycle-wall m={m}", m, cycle_wall(m), results)
    check("torus-wall 12x12", 144, torus_wall(12, 12), results)
    check("hypercube-flux k=7", 128, hypercube_flux(7), results)
    for (n, d, p) in [(200, 3, 0.02), (300, 5, 0.1)]:
        check(f"rand-reg n={n} d={d} p={p}", n, random_regular_signed(n, d, p), results)
    print("ALL OK" if all(results) else "SOME FAIL")
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
