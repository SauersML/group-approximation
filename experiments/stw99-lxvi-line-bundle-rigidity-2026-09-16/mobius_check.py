#!/usr/bin/env python3
"""Sanity check for rordam-line-bundle-sums-are-k-theoretically-rigid.

Model K^0((S^2)^F) = Z[b_i : i in F]/(b_i^2) with basis b_S (S subset F).
[zeta_J] = prod_{i in J} (1 + b_i).  For random finite multisets m of
subsets of F we (1) compute [zeta(m)] by honest ring multiplication,
(2) check the coefficient formula N_m(S) = sum_{J >= S} m(J),
(3) recover m by Moebius inversion, and (4) check that d divides every
coefficient iff d divides every multiplicity.
"""
import itertools, random
from math import gcd
from functools import reduce

def mul(x, y):
    out = {}
    for S, a in x.items():
        for T, b in y.items():
            if S & T:
                continue  # b_i^2 = 0
            U = S | T
            out[U] = out.get(U, 0) + a * b
    return {k: v for k, v in out.items() if v}

def line_class(J):
    x = {frozenset(): 1}
    for i in J:
        x = mul(x, {frozenset(): 1, frozenset([i]): 1})
    return x

def main():
    random.seed(20260916)
    F = range(5)
    subsets = [frozenset(c) for r in range(6) for c in itertools.combinations(F, r)]
    trials = 400
    for _ in range(trials):
        m = {J: random.choice([0, 0, 0, 1, 2, 3, 4, 6]) for J in random.sample(subsets, 6)}
        m = {J: v for J, v in m.items() if v}
        cls = {}
        for J, v in m.items():
            for S, a in line_class(J).items():
                cls[S] = cls.get(S, 0) + v * a
        for S in subsets:
            N = sum(v for J, v in m.items() if S <= J)
            assert cls.get(S, 0) == N
        for T in subsets:
            rec = sum((-1) ** len(S - T) * cls.get(S, 0) for S in subsets if T <= S)
            assert rec == m.get(T, 0), (T, rec, m.get(T, 0))
        gN = reduce(gcd, cls.values(), 0)
        gm = reduce(gcd, m.values(), 0)
        assert gN == gm, (gN, gm)
    print("ok: expansion, Moebius recovery and gcd equality verified on", trials, "random multisets over 5 coordinates")
    # corollary threshold: smallest N with 2^n N > |C| + s N
    for c, s, n in [(0, 1, 1), (3, 1, 1), (5, 2, 2), (10, 3, 2), (7, 7, 3)]:
        N = next(N for N in range(1, 10**6) if (2 ** n) * N > c + s * N)
        print(f"|C|={c} s={s} n={n}: rank 2^n*N={2**n*N} exceeds coordinate bound {c+s*N} at N={N}")

if __name__ == "__main__":
    main()
