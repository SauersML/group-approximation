#!/usr/bin/env python3
"""Seed spread at an A-vertex of the DKKMS 2-to-1 edge law.

Theorem R (`grassmann-restriction-test-is-99-percent-rigid`) transfers to the
DKKMS game only if an A-vertex is tested through *several* of its hyperplanes.
Concretely, write

    w(R | L)  :=  Pr[ the edge's seed is R | the edge's A-space is L ]

for a hyperplane R < L.  If instead `E_L max_R w(R|L)` is close to 1, the test
is blind to the branch coordinate: the labelling

    sigma_L := phi_L,   ker phi_L := argmax_R w(R|L),    tau_R := 0

accepts every edge whose seed is the dominant hyperplane, so it has value
`E_L max_R w(R|L)`, while sigma_L is never the restriction of a fixed functional
on more than about `2^(1-l)` of the L's -- that is, it is far from every locally
honest patchwork.  (Folding constrains which phi are realisable; that is the
remaining hypothesis, see the claim node.)

This script computes `E_L max_R w(R|L)` exactly for the DKKMS edge law, in the
verbatim form of ECCC TR16-198 Section 4.2:

  * U is a k-tuple of variable-disjoint weight-3 equations; X_U = F_2^(3k),
    H_U = span of the k equation vectors, h_U their right-hand sides;
  * V is obtained from U by keeping the i-th equation with probability 1-beta
    and replacing it by one of its three variables, uniformly, with
    probability beta;
  * L' is uniform in Gr(X_V, l-1) and L is uniform in
    { L in Gr(X_U, l) : L > L', L cap H_U = 0 }.

Hence the unnormalised weight of the pair (L, R) is

    S(R)  =  sum over smoothings V2 with R <= X_(V2) of
                 Pr[V2] / |Gr(X_(V2), l-1)|

times a factor that depends only on (l, k), the same for every R < L.  S(R)
factorises over the k blocks except for the |Gr(X_(V2), l-1)| term, which sees
only the number j of smoothed blocks; so S(R) is computed exactly by a DP over
blocks that tracks j.  No sampling of V2 is needed -- only L is sampled.

Run: python3 experiments/grassmann-99-rigidity-2026-09-18/seed_spread_dkkms.py
"""

from __future__ import annotations

import random
import sys
from fractions import Fraction

SEED = 20260918


def gauss_count(n: int, d: int) -> int:
    """|Gr(F_2^n, d)|."""
    if d < 0 or d > n:
        return 0
    num = den = 1
    for i in range(d):
        num *= (1 << (n - i)) - 1
        den *= (1 << (d - i)) - 1
    return num // den


def rref(vectors):
    basis = []
    for v in vectors:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    basis.sort(reverse=True)
    for i, b in enumerate(basis):
        piv = b.bit_length() - 1
        for j, c in enumerate(basis):
            if j != i and (c >> piv) & 1:
                basis[j] = c ^ b
    basis.sort(reverse=True)
    return tuple(basis)


def elements(basis):
    out = [0]
    for b in basis:
        out += [e ^ b for e in out]
    return out


def in_span(v, basis):
    for b in basis:
        v = min(v, v ^ b)
    return v == 0


def hyperplanes(basis):
    """All codimension-1 subspaces of span(basis), as canonical bases.

    A hyperplane is the kernel of a non-zero functional, and a functional is a
    non-zero mask on the coordinates of the canonical basis.
    """
    d = len(basis)
    elts = [e for e in elements(basis) if e]
    coords = {}
    for e in elts:
        v = e
        c = 0
        for i, b in enumerate(basis):
            piv = b.bit_length() - 1
            if (v >> piv) & 1:
                c |= 1 << i
                v ^= b
        assert v == 0
        coords[e] = c
    res = {}
    for mask in range(1, 1 << d):
        ker = [e for e in elts if bin(coords[e] & mask).count("1") % 2 == 0]
        res[rref(ker)] = mask
    return list(res.keys())


class Blocks:
    """k blocks of 3 variables; block i occupies bits 3i, 3i+1, 3i+2."""

    def __init__(self, k: int):
        self.k = k
        self.n = 3 * k
        self.masks = [0b111 << (3 * i) for i in range(k)]
        self.vars = [[1 << (3 * i + t) for t in range(3)] for i in range(k)]
        # H_U: the k equation vectors (the all-ones vector of each block)
        self.H = [self.masks[i] for i in range(k)]

    def block_profile(self, basis, i):
        """Which single variables v of block i satisfy proj_i(span) <= <v>?

        Returns the list of admissible variables (possibly all three when the
        projection is zero, one when it is a line, none otherwise).
        """
        m = self.masks[i]
        proj = {e & m for e in elements(basis)}
        proj.discard(0)
        if not proj:
            return list(self.vars[i])
        if len(proj) == 1:
            p = next(iter(proj))
            return [p] if p in self.vars[i] else []
        return []


def unnormalised_seed_weight(B: Blocks, R_basis, beta: Fraction, l: int):
    """S(R) = sum_{V2 >= R} Pr[V2] / |Gr(X_V2, l-1)|, exactly, by DP on j."""
    # dp[j] = total probability of block choices so far with j smoothed blocks
    dp = [Fraction(0)] * (B.k + 1)
    dp[0] = Fraction(1)
    for i in range(B.k):
        adm = B.block_profile(R_basis, i)
        keep = Fraction(1) - beta
        smooth = beta * Fraction(len(adm), 3)
        nxt = [Fraction(0)] * (B.k + 1)
        for j, p in enumerate(dp):
            if p == 0:
                continue
            nxt[j] += p * keep
            if smooth:
                nxt[j + 1] += p * smooth
        dp = nxt
    total = Fraction(0)
    for j, p in enumerate(dp):
        if p == 0:
            continue
        dimXV = B.n - 2 * j
        g = gauss_count(dimXV, l - 1)
        if g == 0:
            continue
        total += p / g
    return total


def sample_A_vertex(B: Blocks, beta: float, l: int, rng: random.Random):
    """Draw (V, L', L) from the DKKMS edge law; return the basis of L."""
    while True:
        kept = []
        for i in range(B.k):
            if rng.random() < beta:
                kept.append(rng.choice(B.vars[i]))
            else:
                kept += B.vars[i]
        XV = rref(kept)
        if len(XV) < l - 1:
            continue
        # uniform L' in Gr(X_V, l-1): draw l-1 independent vectors of X_V
        XV_elts = [e for e in elements(XV) if e]
        for _ in range(200):
            cand = rref([rng.choice(XV_elts) for _ in range(l - 1)])
            if len(cand) == l - 1:
                Lp = cand
                break
        else:
            continue
        # uniform L > L' in Gr(X_U, l) with L cap H_U = 0
        for _ in range(500):
            x = rng.randrange(1, 1 << B.n)
            if in_span(x, Lp):
                continue
            L = rref(list(Lp) + [x])
            if len(L) != l:
                continue
            if any(in_span(h, L) for h in elements(rref(B.H)) if h):
                continue
            return L, Lp
        continue


def run(k: int, l: int, beta: Fraction, trials: int, rng: random.Random):
    B = Blocks(k)
    tops = []
    dom_is_seed = 0
    for _ in range(trials):
        L, Lp = sample_A_vertex(B, float(beta), l, rng)
        hs = hyperplanes(L)
        ws = [unnormalised_seed_weight(B, R, beta, l) for R in hs]
        tot = sum(ws)
        best = max(ws)
        share = float(best / tot)
        tops.append(share)
        if hs[ws.index(best)] == Lp:
            dom_is_seed += 1
    tops.sort()
    mean = sum(tops) / len(tops)
    med = tops[len(tops) // 2]
    return mean, med, tops[0], tops[-1], dom_is_seed / trials


def main() -> int:
    rng = random.Random(SEED)
    print("E_L max_R w(R|L): the value of the dominant-hyperplane labelling.")
    print("A value near 1 means the DKKMS test is blind to the branch coordinate")
    print("at a typical A-vertex, which refutes 99% rigidity (folding aside).")
    print("A value near 1/(2^l - 1) means the seed is spread over all hyperplanes,")
    print("which is what the six-flag gadget of Theorem R needs.")
    print()
    print(f"{'k':>3} {'l':>3} {'beta':>6} {'uniform':>9} {'mean':>8} {'median':>8}"
          f" {'min':>8} {'max':>8} {'dom=seed':>9}")
    for k in (2, 3, 4, 5):
        for l in (2, 3):
            if 3 * k < l + 2:
                continue
            for beta in (Fraction(1, 10), Fraction(3, 10), Fraction(1, 2)):
                mean, med, lo, hi, dom = run(k, l, beta, 60, rng)
                unif = 1.0 / ((1 << l) - 1)
                print(f"{k:>3} {l:>3} {float(beta):>6.2f} {unif:>9.4f} {mean:>8.4f}"
                      f" {med:>8.4f} {lo:>8.4f} {hi:>8.4f} {dom:>9.2f}")
    print()
    print("trend in k at l = 3 (uniform spread would be 1/7 = 0.1429):")
    for beta in (Fraction(3, 10), Fraction(1, 2)):
        for k in (2, 3, 4, 5, 6, 7, 8):
            mean, med, lo, hi, dom = run(k, 3, beta, 80, rng)
            print(f"  beta={float(beta):.2f} k={k:2d}  mean={mean:.4f} median={med:.4f}"
                  f" min={lo:.4f} max={hi:.4f} dom=seed {dom:.2f}")

    print()
    print("Sanity: with beta = 0 (no smoothing) every hyperplane is a legal seed")
    print("with equal weight, so the share must be exactly 1/(2^l - 1).")
    for k, l in ((3, 2), (3, 3)):
        mean, med, lo, hi, dom = run(k, l, Fraction(0), 20, rng)
        unif = 1.0 / ((1 << l) - 1)
        assert abs(mean - unif) < 1e-12, (mean, unif)
        print(f"  k={k} l={l} beta=0: share = {mean:.6f} = 1/(2^l-1) = {unif:.6f}  OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
