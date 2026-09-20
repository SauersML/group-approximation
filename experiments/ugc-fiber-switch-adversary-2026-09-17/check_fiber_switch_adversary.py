#!/usr/bin/env python3
"""Exact checker for the fiber-plurality switching adversary.

Claim checked: gadgets-into-any-unique-games-stay-below-padding-line.

Source predicate H_b = {(u, v, w) in Z_q^3 : u + v + w = b}, N = q^2 points.
Output alphabet [L] with L >= q (the primaries take values in Z_q, embedded
as 0..q-1).  A witness function is y : H -> [L].

Adversary (randomness xi uniform on Z_q^3, t uniform on (1/q, 1)):
    h*  = (xi1, xi2, b - xi1 - xi2)      (decoded from coordinates 1, 2)
    h'  = (xi1, b - xi1 - xi3, xi3)      (equals h* when xi3 = h*_3)
    s(y) = (1/N) sum_g maxcount of y on the fibre {h : h_3 = g}
    A(y) = y(h') if s(y) > t, else y(h*).

Checked, with exact rationals:
  (P) A(p_j) = xi_j for j = 1, 2, 3, every xi and t (random on primaries);
  (E) A(gamma o y) = gamma(A(y)) for permutations gamma of [L] (equivariance)
      and A(const c) = c;
  (M) for every edge (y, y') differing at one point of H,
      N * Pr[A(y) != A(y')] <= 2 - 1/N.
Exhaustive over all edges for (q, L) = (2, 2), (2, 3), (2, 4), (3, 3);
random plus hill-climbing search for (3, 4), (4, 4), (5, 5), (5, 6), (7, 7).
"""
import itertools
import random
import sys
from fractions import Fraction as Fr


class Setup:
    def __init__(self, q, b=0):
        self.q = q
        self.b = b % q
        self.H = [(u, v, (self.b - u - v) % q) for u in range(q) for v in range(q)]
        self.N = len(self.H)
        self.idx = {h: i for i, h in enumerate(self.H)}
        self.fibres = [[i for i, h in enumerate(self.H) if h[2] == g] for g in range(q)]
        self.lo = Fr(1, q)
        self.width = 1 - self.lo
        # precompute (index of h*, index of h') for every xi
        self.pts = []
        for xi in itertools.product(range(q), repeat=3):
            hs = (xi[0], xi[1], (self.b - xi[0] - xi[1]) % q)
            hp = (xi[0], (self.b - xi[0] - xi[2]) % q, xi[2])
            self.pts.append((xi, self.idx[hs], self.idx[hp]))

    def score(self, y):
        tot = 0
        for fib in self.fibres:
            cnt = {}
            for i in fib:
                cnt[y[i]] = cnt.get(y[i], 0) + 1
            tot += max(cnt.values())
        return Fr(tot, self.N)

    def value(self, y, xi_entry, t):
        _, i_s, i_p = xi_entry
        return y[i_p] if self.score(y) > t else y[i_s]

    def disagree(self, y, z):
        """Exact Pr[A(y) != A(z)] over (xi, t)."""
        sy, sz = self.score(y), self.score(z)
        cuts = sorted({self.lo, Fr(1), max(self.lo, min(sy, 1)), max(self.lo, min(sz, 1))})
        total = Fr(0)
        for xi, i_s, i_p in self.pts:
            for a, bnd in zip(cuts, cuts[1:]):
                if bnd <= a:
                    continue
                tm = (a + bnd) / 2
                va = y[i_p] if sy > tm else y[i_s]
                vb = z[i_p] if sz > tm else z[i_s]
                if va != vb:
                    total += bnd - a
        return total / (len(self.pts) * self.width)


def check_primaries(S):
    prim = [tuple(h[j] for h in S.H) for j in range(3)]
    for entry in S.pts:
        xi = entry[0]
        for t in (S.lo + Fr(1, 10**6), Fr(1, 2) + S.lo / 2, 1 - Fr(1, 10**6)):
            for j in range(3):
                assert S.value(prim[j], entry, t) == xi[j], (S.q, xi, j, t)
    return prim


def check_equivariance(S, L, trials, rng):
    for _ in range(trials):
        y = tuple(rng.randrange(L) for _ in range(S.N))
        gam = list(range(L))
        rng.shuffle(gam)
        gy = tuple(gam[v] for v in y)
        for entry in S.pts:
            for t in (S.lo + Fr(1, 97), Fr(2, 3), 1 - Fr(1, 97)):
                assert S.value(gy, entry, t) == gam[S.value(y, entry, t)]
    for c in range(L):
        y = tuple([c] * S.N)
        for entry in S.pts:
            assert S.value(y, entry, Fr(1, 2) + S.lo / 2) == c


def worst_exhaustive(S, L):
    best = Fr(0)
    arg = None
    for y in itertools.product(range(L), repeat=S.N):
        for x in range(S.N):
            for v in range(y[x] + 1, L):
                z = y[:x] + (v,) + y[x + 1:]
                d = S.disagree(y, z)
                if d > best:
                    best, arg = d, (y, x, v)
    return best, arg


def worst_search(S, L, rng, starts, steps, prim):
    best = Fr(0)
    arg = None
    for s in range(starts):
        # start near a primary-3 anchor, a primary-1 anchor, or at random
        mode = s % 3
        if mode == 0:
            y = list(prim[2])
        elif mode == 1:
            y = list(prim[0])
        else:
            y = [rng.randrange(L) for _ in range(S.N)]
        for _ in range(rng.randrange(S.N + 1)):
            y[rng.randrange(S.N)] = rng.randrange(L)
        y = tuple(y)
        cur = Fr(-1)
        for _ in range(steps):
            x = rng.randrange(S.N)
            v = rng.randrange(L)
            if v == y[x]:
                continue
            z = y[:x] + (v,) + y[x + 1:]
            d = S.disagree(y, z)
            if d > best:
                best, arg = d, (y, x, v)
            # hill-climb on y itself: move to a neighbour whose best edge is not worse
            if d >= cur or rng.random() < 0.05:
                cur = d
                y = z if rng.random() < 0.5 else y
    return best, arg


def main():
    rng = random.Random(20260920)
    ok = True
    out = []
    exhaustive = [(2, 2), (2, 3), (2, 4), (3, 3)]
    searched = [(3, 4, 300, 300), (4, 4, 300, 300), (5, 5, 200, 250), (5, 6, 120, 250), (7, 7, 60, 200)]
    for q, L in exhaustive:
        for b in range(q):
            S = Setup(q, b)
            prim = check_primaries(S)
            check_equivariance(S, L, 30, rng)
            best, arg = worst_exhaustive(S, L)
            bound = Fr(2) - Fr(1, S.N)
            good = S.N * best <= bound
            ok &= good
            out.append(f"exhaustive q={q} L={L} b={b}: max N*Pr = {S.N * best} (= {float(S.N * best):.6f}); "
                       f"bound 2-1/N = {bound}; {'PASS' if good else 'FAIL'}; worst edge {arg}")
    for q, L, starts, steps in searched:
        S = Setup(q, 1 % q)
        prim = check_primaries(S)
        check_equivariance(S, L, 5, rng)
        best, arg = worst_search(S, L, rng, starts, steps, prim)
        bound = Fr(2) - Fr(1, S.N)
        good = S.N * best <= bound
        ok &= good
        out.append(f"search q={q} L={L} b={S.b}: max N*Pr found = {S.N * best} (= {float(S.N * best):.6f}); "
                   f"bound 2-1/N = {bound} (= {float(bound):.6f}); {'PASS' if good else 'FAIL'}")
    for line in out:
        print(line)
    print("ALL PASS" if ok else "SOME FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
