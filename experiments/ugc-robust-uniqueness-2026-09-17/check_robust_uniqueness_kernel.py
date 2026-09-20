#!/usr/bin/env python3
"""Brute-force check of the finite core of `robust-uniqueness-bounds-robust-kernel-rank`.

Core Lemma (checked here).  Let I be a 3LIN instance with equation measure omega
(uniform here) and variable measure nu (uniform here).  Let x be an assignment with
val(x) >= 1 - eps_x.  Let C be a subspace and x* an assignment such that every
assignment of value >= 1 - kappa is nu-rho-close to the coset x* + C  (RU).
Let E_clean be a set of equations with omega(E \\ E_clean) <= p and let Y be any
subspace of homogeneous solutions of E_clean (the image of the coordinate functionals
of an approximate kernel map Phi whose clean equations contain E_clean).
If kappa >= eps_x + p, then
  (a) every y in Y is nu-(2 rho)-close to C;
  (b) if dim Y > dim C, some nonzero w in Y has nu(w != 0) <= 4 rho.
(b) is what makes Phi non-surjective on X_V for all V avoiding supp(w), i.e. on a
mass >= 1 - 3k nu(supp w) >= 1 - 12 k rho of smoothed tuples.

The script takes rho as the smallest radius for which (RU) holds with x* the best
assignment and C a given subspace (the exact homogeneous kernel, or {0}), and checks
(a) and (b) for Y = ker(H restricted to E minus R) over all removal sets R of size
<= 2.  It also runs the J-copy of F_2^4 \\ 0 (all 35 lines), where C is the rank-4
linear kernel: Lemma RU then allows rank 4 and no more, which is the right answer.
Exit code 0 iff every check passes.
"""
import itertools
import random
import sys

import numpy as np


def popcount(arr):
    arr = arr.astype(np.int64)
    c = np.zeros_like(arr)
    while np.any(arr):
        c += arr & 1
        arr >>= 1
    return c


def analyse(N, eqs, rhs, C_list, label, max_remove=2):
    """eqs: list of (u,v,w); rhs: list of bits; C_list: list of ints (subspace)."""
    A = np.arange(1 << N, dtype=np.int64)
    m = len(eqs)
    sat = np.zeros(1 << N, dtype=np.int64)
    hom_bits = []
    for (u, v, w), b in zip(eqs, rhs):
        s = ((A >> u) ^ (A >> v) ^ (A >> w)) & 1
        hom_bits.append(s)
        sat += (s == b)
    val = sat / m
    xstar = int(np.argmax(val))
    eps_x = 1.0 - val[xstar]
    C = np.array(C_list, dtype=np.int64)
    # distance of every assignment to the coset xstar + C
    dist_coset = np.min(popcount(A[:, None] ^ (xstar ^ C)[None, :]), axis=1) / N
    dist_C = np.min(popcount(A[:, None] ^ C[None, :]), axis=1) / N
    hom = np.array(hom_bits)  # m x 2^N
    rC = int(round(np.log2(len(C_list))))
    checks = 0
    btrig = 0
    for s in range(max_remove + 1):
        for R in itertools.combinations(range(m), s):
            p = s / m
            kappa = eps_x + p
            near = val >= 1 - kappa - 1e-12
            rho = float(np.max(dist_coset[near]))
            keep = [i for i in range(m) if i not in R]
            inY = np.all(hom[keep] == 0, axis=0)
            Y = A[inY]
            dimY = int(round(np.log2(len(Y))))
            # (a)
            worst = float(np.max(dist_C[Y]))
            if worst > 2 * rho + 1e-12:
                print(f"FAIL (a) {label} R={R}: y at distance {worst} > 2 rho = {2*rho}")
                return False
            # (b)
            if dimY > rC:
                btrig += 1
                wts = popcount(Y[Y != 0]) / N
                if float(np.min(wts)) > 4 * rho + 1e-12:
                    print(f"FAIL (b) {label} R={R}: dimY={dimY} > {rC}, min wt {np.min(wts)} > 4 rho")
                    return False
            checks += 1
    print(f"PASS {label}: N={N} m={m} eps_x={eps_x:.3f} dimC={rC} checks={checks} (b)-triggered={btrig}")
    return True


def span(vecs):
    S = {0}
    for v in vecs:
        S |= {s ^ v for s in S}
    return sorted(S)


def random_instance(N, m, noise, rng):
    xs = rng.getrandbits(N)
    eqs, rhs = [], []
    for _ in range(m):
        u, v, w = rng.sample(range(N), 3)
        b = ((xs >> u) ^ (xs >> v) ^ (xs >> w)) & 1
        if rng.random() < noise:
            b ^= 1
        eqs.append((u, v, w))
        rhs.append(b)
    return eqs, rhs


def exact_kernel(N, eqs):
    A = np.arange(1 << N, dtype=np.int64)
    ok = np.ones(1 << N, dtype=bool)
    for (u, v, w) in eqs:
        ok &= (((A >> u) ^ (A >> v) ^ (A >> w)) & 1) == 0
    return [int(a) for a in A[ok]]


def main():
    rng = random.Random(20260917)
    ok = True
    for trial in range(12):
        N = rng.choice([9, 10, 11])
        m = rng.choice([2 * N, 3 * N])
        eqs, rhs = random_instance(N, m, rng.choice([0.0, 0.05]), rng)
        K = exact_kernel(N, eqs)
        ok &= analyse(N, eqs, rhs, K, f"random#{trial} (C = exact kernel)")
        if len(K) > 1:
            # also test with C = {0}: RU then may fail (large rho) but (a),(b) must still hold
            ok &= analyse(N, eqs, rhs, [0], f"random#{trial} (C = 0)")
    # J-copy of F_2^4 \ 0: points 1..15 -> variables 0..14, one equation per line
    n = 4
    pts = list(range(1, 1 << n))
    idx = {p: i for i, p in enumerate(pts)}
    lines = set()
    for a in pts:
        for b in pts:
            if a < b:
                lines.add(tuple(sorted((a, b, a ^ b))))
    eqs = [(idx[a], idx[b], idx[c]) for (a, b, c) in sorted(lines)]
    rhs = [0] * len(eqs)
    K = exact_kernel(len(pts), eqs)
    assert len(K) == 16, len(K)
    ok &= analyse(len(pts), eqs, rhs, K, "J-copy n=4 (C = linear kernel, rank 4)", max_remove=1)
    print("ALL PASS" if ok else "SOME FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
