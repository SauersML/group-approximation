#!/usr/bin/env python3
"""Checks for dkkms-near-perfect-labellings-are-outer-honest.

1. Spectral gap (Step 1 of the route).  For small (N, d) build the down-up
   walk W_d on Gr(F_2^N, d) (L1 -> random hyperplane M of L1 -> random
   d-space L2 containing M) and check that its second eigenvalue is at most
   u_d = (2^(d-1) - 1) / (2^d - 1) < 1/2, the bound proved by the recursion.

2. Rigidity (Step 2).  For linear tables F on Gr(F_2^N, l) with structured and
   random corruptions compute exactly
       delta = Pr_{L' ; L1, L2 > L'} [ F[L1]|L' != F[L2]|L' ]
   and dist = min over linear g of Pr_L [ F[L] != g|L ], and check
   dist <= 20 delta.  Also check that the decoder of the proof (plurality
   g(z), then the nearest linear function) attains a distance <= 20 delta.

3. Folding invariance (Step 3).  On X = F_2^6 with H = span of two disjoint
   weight-3 vectors and a right-hand side h, build (H,h)-invariant tables from
   class labels (one extension of h per class M = L + H), corrupt some classes,
   and check: whenever omega = Pr_{L valid}[F[L] != g|L] < 3/8 for the
   nearest linear g, one has g|H = h.
"""
import itertools
import random
import sys

import numpy as np


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return frozenset(s)


def grassmannian(N, d):
    """All d-dimensional subspaces of F_2^N as frozensets of ints."""
    out = set()
    level = {frozenset({0})}
    for _ in range(d):
        nxt = set()
        for S in level:
            for v in range(1, 1 << N):
                if v not in S:
                    nxt.add(frozenset(S | {x ^ v for x in S}))
        level = nxt
    out = sorted(level, key=lambda S: tuple(sorted(S)))
    return out


def par(x):
    return bin(x).count("1") & 1


def hyperplanes(L):
    """Codimension-1 subspaces of the subspace L (a frozenset)."""
    elems = sorted(L)
    res = set()
    # hyperplanes of L <-> nonzero functionals on L; use kernels of g|L
    nb = max(elems).bit_length()
    for g in range(1, 1 << nb):
        ker = frozenset(z for z in elems if par(g & z) == 0)
        if len(ker) * 2 == len(elems):
            res.add(ker)
    return sorted(res, key=lambda S: tuple(sorted(S)))


def check_spectral(N, d):
    top = grassmannian(N, d)
    low = grassmannian(N, d - 1)
    ti = {S: i for i, S in enumerate(top)}
    li = {S: i for i, S in enumerate(low)}
    ext = {S: [] for S in low}
    hyp = {}
    for L in top:
        hs = hyperplanes(L) if d > 1 else [frozenset({0})]
        hyp[L] = hs
        for M in hs:
            ext[M].append(L)
    W = np.zeros((len(top), len(top)))
    for L1 in top:
        hs = hyp[L1]
        for M in hs:
            e = ext[M]
            for L2 in e:
                W[ti[L1], ti[L2]] += 1.0 / (len(hs) * len(e))
    ev = np.sort(np.linalg.eigvalsh((W + W.T) / 2))[::-1]
    assert abs(ev[0] - 1) < 1e-9 and ev[1] < 1 - 1e-9
    u = (2 ** (d - 1) - 1) / (2 ** d - 1)
    ok = ev[1] <= u + 1e-9
    return len(top), ev[1], u, ok


def restrict(g, L):
    return frozenset(z for z in L if par(g & z))


def rigidity_instance(N, l, F, top, low, ext):
    """F: dict L -> frozenset of z in L with value 1 (a linear functional)."""
    rej = 0.0
    for M in low:
        e = ext[M]
        w = 1.0 / (len(low) * len(e) * len(e))
        for L1 in e:
            a = F[L1] & M
            for L2 in e:
                if a != (F[L2] & M):
                    rej += w
    best = 1.0
    for g in range(1 << N):
        bad = sum(1 for L in top if F[L] != restrict(g, L)) / len(top)
        best = min(best, bad)
    # proof decoder: plurality g(z) over L containing z, then nearest linear
    votes = {}
    for L in top:
        for z in L:
            if z:
                c = votes.setdefault(z, [0, 0])
                c[1 if z in F[L] else 0] += 1
    gz = {z: (1 if c[1] > c[0] else 0) for z, c in votes.items()}
    gz[0] = 0
    ghat = max(range(1 << N), key=lambda a: sum(1 for z in gz if gz[z] == par(a & z)))
    dec = sum(1 for L in top if F[L] != restrict(ghat, L)) / len(top)
    return rej, best, dec


def check_rigidity(N, l, trials, rng):
    top = grassmannian(N, l)
    low = grassmannian(N, l - 1)
    ext = {S: [] for S in low}
    for L in top:
        for M in (hyperplanes(L) if l > 1 else [frozenset({0})]):
            ext[M].append(L)
    worst = 0.0
    worst_dec = 0.0
    nontriv = 0
    for t in range(trials):
        g0 = rng.randrange(1 << N)
        g1 = g0 ^ (1 + rng.randrange((1 << N) - 1))
        F = {L: restrict(g0, L) for L in top}
        mode = t % 4
        if mode == 0:  # random functionals on a random fraction of L
            frac = rng.choice([0.01, 0.03, 0.1, 0.3])
            for L in top:
                if rng.random() < frac:
                    F[L] = restrict(rng.randrange(1 << N), L)
        elif mode == 1:  # second global function on L containing a vector
            v = 1 + rng.randrange((1 << N) - 1)
            for L in top:
                if v in L:
                    F[L] = restrict(g1, L)
        elif mode == 2:  # second global function on L inside a hyperplane
            h = 1 + rng.randrange((1 << N) - 1)
            for L in top:
                if all(par(h & z) == 0 for z in L):
                    F[L] = restrict(g1, L)
        else:  # adversarial: flip on L meeting a small set of points
            pts = set(rng.sample(range(1, 1 << N), 2))
            for L in top:
                if L & pts:
                    F[L] = restrict(g1, L)
        rej, best, dec = rigidity_instance(N, l, F, top, low, ext)
        if rej > 0:
            nontriv += 1
            worst = max(worst, best / rej)
            worst_dec = max(worst_dec, dec / rej)
        assert best <= 20 * rej + 1e-12, (N, l, t, rej, best)
        assert dec <= 20 * rej + 1e-12, (N, l, t, rej, dec)
    return len(top), nontriv, worst, worst_dec


def check_folding(trials, rng, l=2):
    N = 6
    xe = [0b000111, 0b111000]
    H = span(xe)
    top = grassmannian(N, l)
    valid = [L for L in top if len(L & H) == 1]
    low = grassmannian(N, l - 1)
    ext = {S: [] for S in low}
    for L in top:
        for M in hyperplanes(L):
            ext[M].append(L)
    fails = 0
    decisive = 0
    for t in range(trials):
        b = [rng.randrange(2), rng.randrange(2)]
        # a global g satisfying h: g(x_e) = b_e
        sols = [g for g in range(1 << N) if [par(g & x) for x in xe] == b]
        g0 = rng.choice(sols)
        classes = {}
        for L in valid:
            M = frozenset(x ^ y for x in L for y in H)
            classes.setdefault(M, []).append(L)
        frac = rng.choice([0.02, 0.05, 0.1, 0.2, 0.4, 0.7])
        lab = {}
        for M in classes:
            if rng.random() < frac:
                lab[M] = rng.choice(sols)  # another extension of h on M
            else:
                lab[M] = g0
        F = {}
        for M, Ls in classes.items():
            for L in Ls:
                F[L] = restrict(lab[M], L)
        for L in top:
            if L not in F:
                F[L] = frozenset()  # invalid L: arbitrary (zero)
        # invariance check: F[L] is the restriction of one extension of h
        for M, Ls in classes.items():
            for L in Ls:
                assert F[L] == restrict(lab[M], L)
        rej, best, _ = rigidity_instance(N, l, F, top, low, ext)
        assert best <= 20 * rej + 1e-12
        # nearest linear g over valid L, and the invariance conclusion
        def omega(g):
            return sum(1 for L in valid if F[L] != restrict(g, L)) / len(valid)
        gbest = min(range(1 << N), key=omega)
        if omega(gbest) < 3 / 8:
            decisive += 1
            if [par(gbest & x) for x in xe] != b:
                fails += 1
        # also every g violating h has omega >= 3/8 on invariant tables
        for g in range(1 << N):
            if [par(g & x) for x in xe] != b:
                assert omega(g) >= (1 - 2 ** (-l)) / 2 - 1e-12, (t, g, omega(g))
    return decisive, fails


def main():
    rng = random.Random(20260918)
    print("[1] spectral gap of the down-up walk W_d on Gr(F_2^N, d)")
    for N, d in [(3, 1), (3, 2), (4, 2), (4, 3), (5, 2), (5, 3), (6, 2), (6, 3), (7, 2)]:
        n, lam2, u, ok = check_spectral(N, d)
        print(f"  N={N} d={d} |Gr|={n:5d} lambda2={lam2:.6f} bound u_d={u:.6f} ok={ok}")
        assert ok
    print("[2] rigidity of linear tables: dist <= 20 delta")
    for N, l, tr in [(4, 2, 40), (5, 2, 40), (5, 3, 24), (6, 2, 24), (6, 3, 12)]:
        n, nt, w, wd = check_rigidity(N, l, tr, rng)
        print(f"  N={N} l={l} |Gr|={n:5d} nontrivial={nt:3d} max dist/delta={w:.3f} max decoder/delta={wd:.3f}")
    print("[3] folding invariance: omega < 3/8 forces g|H = h")
    dec, fails = check_folding(30, rng)
    print(f"  decisive trials={dec} failures={fails}")
    assert fails == 0
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    sys.exit(main())
