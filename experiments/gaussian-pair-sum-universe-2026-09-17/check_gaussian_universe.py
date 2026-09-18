#!/usr/bin/env python3
"""Checks for gaussian-pair-resampling-partitions-are-unstable and
gaussian-pair-sum-universe-gives-robust-rich-2to1-sdp-gaps.

Sections
  A. exact crossing law of a uniform perfect matching vs the two tail bounds
     used in Lemma E (small-set bound and sequential Chernoff bound);
  B. the union bound eps_n of Lemma E with (j, h0, theta) = (40, 1/100, 1/4):
     both regime bases and eps_n for several n (log-space, exact sums);
  C. Lemma N: ||D x||^2 <= 1 - lambda_2(L_H) / (2 j^2) on 1-perp for products
     D of random matching projections, and the Mehler covariance identity;
  D. SDP objective of the polar-orthonormalised Gaussian solution -> 1 in d;
  E. Monte Carlo value of the linear strategy in the Gaussian game at d = 1.
Seed 20260918. Exit code 0 iff every assertion holds.
"""
import math
import sys

import numpy as np

rng = np.random.default_rng(20260918)
ok = True


def check(cond, msg):
    global ok
    if not cond:
        ok = False
        print("FAIL:", msg)


def lgamma_dfact(m):
    """log((m-1)!!) for even m >= 0, i.e. number of perfect matchings on m points."""
    if m == 0:
        return 0.0
    k = m // 2
    return math.lgamma(m + 1) - k * math.log(2) - math.lgamma(k + 1)


def crossing_law(N, s):
    """exact P[e_P(S) = t] for |S| = s in a uniform perfect matching of [N]."""
    out = {}
    tot = lgamma_dfact(N)
    for t in range(0, min(s, N - s) + 1):
        if (s - t) % 2 or (N - s - t) % 2:
            continue
        lw = (math.lgamma(s + 1) - math.lgamma(t + 1) - math.lgamma(s - t + 1)
              + math.lgamma(N - s + 1) - math.lgamma(t + 1) - math.lgamma(N - s - t + 1)
              + math.lgamma(t + 1) + lgamma_dfact(s - t) + lgamma_dfact(N - s - t) - tot)
        out[t] = math.exp(lw)
    return out


def kl(a, b):
    return a * math.log(a / b) + (1 - a) * math.log((1 - a) / (1 - b))


J, H0, THETA = 40, 0.01, 0.25
DKL = kl(2 * H0, 0.25)

# ---------------- A. crossing law vs bounds ----------------
print("A. exact crossing tails vs Lemma E bounds")
worst_small, worst_lin = 0.0, 0.0
for n in [8, 16, 40, 100]:
    N = 2 * n
    for s in range(1, n + 1):
        law = crossing_law(N, s)
        check(abs(sum(law.values()) - 1) < 1e-9, f"law sums to 1 (n={n}, s={s})")
        tail = sum(p for t, p in law.items() if t < H0 * s)
        x = s / n
        m0 = math.ceil(s * (1 - H0) / 2)
        if s <= THETA * n:
            # small-set bound (s^2/2)^m0 / (m0! n^m0), valid for s <= n
            b = math.exp(m0 * math.log(s * s / 2.0) - math.lgamma(m0 + 1) - m0 * math.log(n)) if s >= 2 else 0.0
            check(tail <= b + 1e-15, f"small bound n={n} s={s}")
            if b > 0:
                worst_small = max(worst_small, tail / b)
        # sequential Chernoff bound, valid for all s <= n
        bl = math.exp(-(s / 2.0) * DKL)
        check(tail <= bl + 1e-15, f"chernoff bound n={n} s={s}")
        worst_lin = max(worst_lin, tail / bl)
print(f"   max tail/small-bound = {worst_small:.3e}, max tail/chernoff-bound = {worst_lin:.3e}")

# ---------------- B. the union bound ----------------
print("B. union bound constants, j=40, h0=1/100, theta=1/4")
def small_base(x):
    return (2 * math.e / x) * (math.e * x / (1 - H0)) ** (J * (1 - H0) / 2)
lin_base = (2 * math.e / THETA) * math.exp(-J * DKL / 2)
print(f"   small-regime base at x=1/4: {small_base(0.25):.4f}; linear base: {lin_base:.4f}; D = {DKL:.4f}")
check(small_base(0.25) <= 0.5 and lin_base <= 0.5, "both bases <= 1/2")
check(math.e * THETA / (1 - H0) <= 1, "small-regime inner base <= 1")
prev = None
for n in [100, 1000, 10**4, 10**5]:
    eps = 0.0
    for s in range(2, n + 1):
        x = s / n
        if s <= THETA * n:
            eps += math.exp(s * math.log(small_base(x)))
        else:
            eps += lin_base ** s
    print(f"   n={n:>6}: eps_n <= {eps:.3e}")
    if prev is not None:
        check(eps < prev, "eps_n decreasing")
    prev = eps

# ---------------- C. product-of-projections lemma ----------------
print("C. Lemma N on random matching products")
def matching(N):
    p = rng.permutation(N)
    return p.reshape(-1, 2)

def proj(N, M):
    Pi = np.zeros((N, N))
    for a, b in M:
        Pi[a, a] = Pi[b, b] = Pi[a, b] = Pi[b, a] = 0.5
    return Pi

for n, j in [(6, 3), (16, 3), (16, 10), (40, 40)]:
    N = 2 * n
    one = np.ones(N) / math.sqrt(N)
    Q = np.linalg.svd(np.eye(N) - np.outer(one, one))[0][:, : N - 1]  # basis of 1-perp
    worst = -1.0
    for _ in range(20):
        Ms = [matching(N) for _ in range(j)]
        Pis = [proj(N, M) for M in Ms]
        D = np.eye(N)
        for Pi in Pis:
            D = Pi @ D
        L = sum(2 * (np.eye(N) - Pi) for Pi in Pis)
        lam2 = np.sort(np.linalg.eigvalsh(Q.T @ L @ Q))[0]
        r2 = np.linalg.norm(Q.T @ D @ Q, 2) ** 2
        check(np.allclose(D @ np.ones(N), np.ones(N)), "D fixes 1")
        check(r2 <= 1 - lam2 / (2 * j * j) + 1e-10, f"Lemma N n={n} j={j}")
        worst = max(worst, r2 - (1 - lam2 / (2 * j * j)))
        # Mehler composition: noise covariance of T_{Pi_1} ... T_{Pi_j} is I - D D^T
        cov = np.zeros((N, N))
        A = np.eye(N)
        for Pi in Pis:  # x -> Pi x + (I - Pi) x'
            cov = Pi @ cov @ Pi.T + (np.eye(N) - Pi)
            A = Pi @ A
        check(np.allclose(cov, np.eye(N) - D @ D.T), "Mehler covariance identity")
    print(f"   n={n:>3} j={j:>2}: max (||D'||^2 - (1 - lam2/(2j^2))) = {worst:.3e} (must be <= 0)")

# ---------------- D. SDP objective ----------------
print("D. SDP objective of polar-orthonormalised Gaussian solution")
def polar(X):
    U, _, Vt = np.linalg.svd(X, full_matrices=False)
    return U @ Vt

n = 4
for d in [16, 64, 256, 1024, 4096]:
    vals = []
    for _ in range(400):
        X = rng.standard_normal((2 * n, d)) / math.sqrt(d)
        M = matching(2 * n)
        Y = np.array([X[a] + X[b] for a, b in M])
        UX, UY = polar(X), polar(Y)
        obj = 0.0
        for bi, (a, b) in enumerate(M):
            obj += UX[a] @ UY[bi] + UX[b] @ UY[bi]
        vals.append(obj / (n * math.sqrt(2)))
    print(f"   n=4 d={d:>5}: mean SDP objective = {np.mean(vals):.5f}")
    if d == 4096:
        check(np.mean(vals) > 0.99, "SDP objective near 1 at large d")

# ---------------- E. linear strategy value, d = 1 ----------------
print("E. value of the linear strategy (argmax g_a, argmax pair sum), d = 1")
for n in [4, 16, 64, 256, 1024, 4096]:
    trials = 4000
    hit = 0
    for _ in range(trials):
        g = rng.standard_normal(2 * n)
        M = matching(2 * n)
        h = g[M[:, 0]] + g[M[:, 1]]
        a = int(np.argmax(g))
        b = int(np.argmax(h))
        hit += a in (M[b, 0], M[b, 1])
    print(f"   n={n:>5}: value ~ {hit / trials:.4f}")

print("all checks passed" if ok else "SOME CHECKS FAILED")
sys.exit(0 if ok else 1)
