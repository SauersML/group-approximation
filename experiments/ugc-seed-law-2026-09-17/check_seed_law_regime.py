#!/usr/bin/env python3
"""Exact conditional seed law of the DKKMS 2-to-1 edge process at an A-vertex.

DKKMS (ECCC TR16-198, Sec. 4.2) edge process, quoted in
research/dkkms-near-perfect-labellings-are-outer-honest-proof.md (Q2):
  1. U = k equations; V keeps equation i w.p. 1-beta, else one of its 3
     variables (uniformly).  X_U = F_2^(3k), X_V = vectors supported on V.
  2. L' uniform in Gr(X_V, l-1), L uniform l-space of X_U containing L'.
  Restrict to L cap H_U = 0.

Given (U, L), the seed L' = R is a hyperplane of L and
  w(R | U, L)  propto  E_V [ 1{R <= X_V} / |Gr(X_V, l-1)| ]
(the extension count N and the validity factor do not depend on R).
Per block i let c_i(R) = 3 if pi_i(R) = 0, 1 if pi_i(R) = span(e_j), else 0.
Then, with n1, n3 the numbers of blocks with c_i = 1, 3,
  w(R) propto sum_s [z^s] (1-b)^(k-n1-n3) (1-b+b z/3)^n1 (1-b+b z)^n3
                    * G(3k, l-1) / G(3k-2s, l-1),
with G the Gaussian binomial.  Everything below is exact up to float rounding;
only L is sampled.

Checks:
  (a) at beta = 1/2 the law concentrates on one hyperplane as k grows
      (the regime measured by e2-w2-ugc-selector-kill);
  (b) at the DKKMS choice beta = log log k / k the law tends to uniform on the
      2^l - 1 hyperplanes, with TV of order beta sqrt(k) 2^(l-1), i.e. inside
      the covering error SD* of Theorem R.
  (c) the Corollary-A admissibility threshold k_A(l) (eps_k <= p0^2/4 with
      eps_k = exp(-k/exp(q l))) versus the Theorem R threshold k_0(l)
      (SD* <= 1e-5), for q = 1, 2.
"""
import math
import random

import numpy as np

SEED = 20260918


def log_gauss_ratio(n, d, s):
    """log( G(n,d) / G(n-2s,d) ) for Gaussian binomials over F_2."""
    def lg(m):  # log(2^m - 1), m >= 1
        return m * math.log(2.0) + math.log1p(-2.0 ** -m)
    return sum(lg(n - j) - lg(n - 2 * s - j) for j in range(d))


def log_weight(k, l, beta, n1, n3):
    """log of sum_s coef_s * G(3k,l-1)/G(3k-2s,l-1)."""
    n0 = k - n1 - n3
    terms = []
    for a in range(n1 + 1):          # smoothed blocks among the c=1 blocks
        la = (math.lgamma(n1 + 1) - math.lgamma(a + 1) - math.lgamma(n1 - a + 1)
              + a * math.log(beta / 3) + (n1 - a) * math.log(1 - beta))
        for c in range(n3 + 1):      # smoothed blocks among the c=3 blocks
            s = a + c
            if 3 * k - 2 * s < l - 1:
                continue
            lc = (math.lgamma(n3 + 1) - math.lgamma(c + 1) - math.lgamma(n3 - c + 1)
                  + c * math.log(beta) + (n3 - c) * math.log(1 - beta))
            terms.append(la + lc + log_gauss_ratio(3 * k, l - 1, s))
    m = max(terms)
    return n0 * math.log(1 - beta) + m + math.log(sum(math.exp(t - m) for t in terms))


UNIT = {1, 2, 4}


def seed_law(k, l, beta, rng):
    """Sample L (with L cap H_U = 0) and return the normalised seed law."""
    while True:
        B = rng.integers(0, 8, size=(l, k))          # block i of basis vector j, as 3 bits
        # L cap H_U = 0: no nonzero combination lies in H_U (every block in {0,7}).
        ok = True
        for a in range(1, 2 ** l):
            v = np.zeros(k, dtype=np.int64)
            for j in range(l):
                if a >> j & 1:
                    v ^= B[j]
            if np.all((v == 0) | (v == 7)):
                ok = False
                break
        if ok:
            break
    combos = {}
    for a in range(1, 2 ** l):
        v = np.zeros(k, dtype=np.int64)
        for j in range(l):
            if a >> j & 1:
                v ^= B[j]
        combos[a] = v
    logs = []
    for phi in range(1, 2 ** l):                     # hyperplane R = ker(phi)
        elems = [combos[a] for a in range(1, 2 ** l) if bin(a & phi).count("1") % 2 == 0]
        E = np.stack(elems)                          # nonzero elements of R, block-wise
        nz = E != 0
        allzero = ~nz.any(axis=0)
        # pi_i(R) = span(e_j): every nonzero entry equals one unit vector
        first = np.where(nz, E, 0).max(axis=0)
        same = np.all((E == 0) | (E == first), axis=0)
        unit = np.isin(first, list(UNIT)) & same & ~allzero
        n3 = int(allzero.sum())
        n1 = int(unit.sum())
        logs.append(log_weight(k, l, beta, n1, n3))
    m = max(logs)
    w = np.exp(np.array(logs) - m)
    return w / w.sum()


def stats(k, l, beta, trials, rng):
    mx, tv = [], []
    u = 1.0 / (2 ** l - 1)
    for _ in range(trials):
        p = seed_law(k, l, beta, rng)
        mx.append(p.max())
        tv.append(0.5 * np.abs(p - u).sum())
    return float(np.mean(mx)), float(np.mean(tv))


def main():
    rng = np.random.default_rng(SEED)
    random.seed(SEED)
    l = 3
    u = 1 / 7
    print("(a) beta = 1/2, l = 3: E max share (uniform = %.4f)" % u)
    prev = 0.0
    rows_a = []
    for k in [2, 4, 6, 8]:
        mx, tv = stats(k, l, 0.5, 400, rng)
        rows_a.append((k, mx))
        print("   k=%2d  E max=%.3f  E TV=%.3f" % (k, mx, tv))
    assert rows_a[-1][1] > 0.6, "expected concentration at beta=1/2"
    assert rows_a[-1][1] > rows_a[0][1]

    print("(b) beta = ln ln k / k, l = 3")
    rows_b = []
    for k in [16, 128, 1024, 8192]:
        beta = math.log(math.log(k)) / k
        mx, tv = stats(k, l, beta, 120, rng)
        pred = beta * math.sqrt(k) * 2 ** (l - 1)
        rows_b.append((k, mx, tv, pred))
        print("   k=%6d beta=%.2e  E max=%.4f  E TV=%.4f  beta*sqrt(k)*2^(l-1)=%.4f"
              % (k, beta, mx, tv, pred))
    tvs = [r[2] for r in rows_b]
    assert all(tvs[i + 1] < tvs[i] for i in range(len(tvs) - 1)), "TV must decrease"
    assert rows_b[-1][1] < u + 0.02, "seed law must approach uniform"
    for k, mx, tv, pred in rows_b:
        assert tv <= pred, "TV must sit inside the covering-scale bound"

    print("(b') l = 4, beta = ln ln k / k (uniform = %.4f)" % (1 / 15))
    for k in [64, 1024]:
        beta = math.log(math.log(k)) / k
        mx, tv = stats(k, 4, beta, 20, rng)
        print("   k=%6d  E max=%.4f  E TV=%.4f  pred=%.4f" % (k, mx, tv, beta * math.sqrt(k) * 8))

    print("(c) thresholds: k_A(l) from exp(-k/exp(q l)) <= p0^2/4; k_0(l) from SD* <= 1e-5")

    def k0(l):
        k = 16
        while (math.log(math.log(k)) / k) * math.sqrt(k) * 2 ** (l + 3) + 3 * 2.0 ** (l - k) > 1e-5:
            k *= 1.05
        return k

    for q in [1, 2]:
        first = None
        for L in range(3, 200):
            p0 = 2.0 ** -L / 192
            kA = math.exp(q * L) * math.log(4 / p0 ** 2)
            if kA >= k0(L) and first is None:
                first = L
        print("   q=%d: k_A(l) >= k_0(l) from l = %s on (checked l < 200)" % (q, first))
        if q == 2:
            assert first == 43, "Corollary S3 quotes l >= 43"
            assert first is not None and all(
                math.exp(2 * L) * math.log(4 * (192 * 2.0 ** L) ** 2) >= k0(L) for L in range(first, 200))
        if q == 1:
            assert first is None
    print("all checks pass")


if __name__ == "__main__":
    main()
