#!/usr/bin/env python3
"""Numerical checks for the Gaussian pair-sum universe rich 2-to-1 game.

(i)   lambda_k = || E_P Pi_P^{(x)k} ||  on (1^perp)^{(x)k}, exactly, for small n,
      where Pi_P = (I + sigma_P)/2 and sigma_P is the partner involution of a
      uniform perfect matching of [2n].  Compared with the limit 2^-ceil(k/2)
      and with the closed form lambda_1 = (n-1)/(2n-1).
(ii)  Monte Carlo of the basic-SDP objective of the polar-frame vectors
      z(G,a) = polar(G)_a / sqrt(2n), z(H,b) = polar(H)_b / sqrt(n), H = G M_P,
      as d grows (n fixed).  It should tend to 1.
(iii) Monte Carlo value of the linear strategy A = argmax_a <g_a,w>,
      B = argmax_b <h_b,w> (reference only; the proof bounds every strategy).
Seed 20260917.  Runtime: well under a minute.
"""
import itertools
import math

import numpy as np


def matchings(m):
    """All perfect matchings of range(m), as partner arrays."""
    if m == 0:
        yield []
        return
    def rec(rest):
        if not rest:
            yield {}
            return
        a = rest[0]
        for j in range(1, len(rest)):
            b = rest[j]
            sub = rest[1:j] + rest[j + 1:]
            for mm in rec(sub):
                d = dict(mm)
                d[a] = b
                d[b] = a
                yield d
    for d in rec(list(range(m))):
        yield [d[i] for i in range(m)]


def lam(n, k):
    m = 2 * n
    I = np.eye(m)
    Mk = np.zeros((m ** k, m ** k))
    count = 0
    for p in matchings(m):
        sig = np.zeros((m, m))
        sig[np.arange(m), p] = 1.0
        Pi = (I + sig) / 2
        A = Pi
        for _ in range(k - 1):
            A = np.kron(A, Pi)
        Mk += A
        count += 1
    Mk /= count
    C = I - np.ones((m, m)) / m
    Ck = C
    for _ in range(k - 1):
        Ck = np.kron(Ck, C)
    ev = np.linalg.eigvalsh(Ck @ Mk @ Ck)
    return ev[-1]


def polar(A):
    U, _, Vt = np.linalg.svd(A, full_matrices=False)
    return U @ Vt


def sdp_objective(n, d, trials, rng):
    m = 2 * n
    tot = 0.0
    for _ in range(trials):
        perm = rng.permutation(m)
        P = np.empty(m, dtype=int)
        P[perm] = np.arange(m) // 2          # uniform labelled 2-to-1 map
        M = np.zeros((m, n))
        M[np.arange(m), P] = 1.0
        G = rng.standard_normal((d, m))
        X = polar(G)
        Y = polar(G @ M)
        tot += sum(X[:, a] @ Y[:, P[a]] for a in range(m)) / (math.sqrt(2) * n)
    return tot / trials


def linear_value(n, trials, rng):
    m = 2 * n
    hit = 0
    for _ in range(trials):
        perm = rng.permutation(m)
        P = np.empty(m, dtype=int)
        P[perm] = np.arange(m) // 2
        g = rng.standard_normal(m)          # <g_a, w> for a fixed unit w
        h = np.zeros(n)
        np.add.at(h, P, g)
        hit += P[np.argmax(g)] == np.argmax(h)
    return hit / trials


def main():
    rng = np.random.default_rng(20260917)
    print("(i) exact lambda_k on (1^perp)^k ; limit 2^-ceil(k/2)")
    print(" n k   lambda_k    2^-ceil(k/2)   (n-1)/(2n-1)")
    for n, ks in [(2, [1, 2, 3, 4]), (3, [1, 2, 3, 4]), (4, [1, 2, 3]),
                  (5, [1, 2, 3])]:
        for k in ks:
            l = lam(n, k)
            print(f"{n:2d} {k:1d}  {l:.6f}   {2.0 ** -math.ceil(k / 2):.6f}"
                  f"      {(n - 1) / (2 * n - 1):.6f}")
            if k == 1:
                assert abs(l - (n - 1) / (2 * n - 1)) < 1e-9
    print("(ii) polar-frame SDP objective, n = 3")
    for d in [6, 24, 96, 384, 1536]:
        print(f" d={d:5d}  objective={sdp_objective(3, d, 400, rng):.5f}")
    print("(iii) linear strategy value (d irrelevant)")
    for n in [4, 16, 64, 256]:
        print(f" n={n:4d}  val_linear={linear_value(n, 20000, rng):.4f}")


if __name__ == "__main__":
    main()
