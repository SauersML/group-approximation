#!/usr/bin/env python3
"""Exact replay of the degree-product shift overlay used in
research/spectral-gap-ratio-reductions-cannot-prove-ugc.md.

For a weighted unique game U on alphabet Z_k (loops allowed, no isolated
vertices, total weight W, weighted degrees deg with a loop counted once,
vol = sum deg), the overlay O_c adds, for every unordered pair u != v and every
shift a in Z_k, the constraint x_v = x_u + a with weight
c deg(u) deg(v) / (vol k).  Claims checked:

  (A) per labeling x: val'(x) = (W val(x) + Omega/k) / (W + Omega), where Omega
      is the total overlay weight, and 0 < Omega <= cW            (exact rationals)
  (B) val(U) / (1 + c) <= val(U') <= max(val(U), 1/k)        (exact rationals)
  (C) lambda_2 of the normalized Laplacian of U' >= c (1 + 2c) / (1 + c)^3,
      and >= 3c / (4 (1 + c)) when U has no loops (floating point, tolerance
      1e-9); for weighted-regular U also lambda_2 >= c / (1 + c)
  (D) val(U) >= 1/k when U has no loops (exact); with loops it can fail, and
      the replay records such cases (so the max in (B) is needed)

Exit code 0 iff every check passes.
"""
import itertools
import random
from fractions import Fraction

import numpy as np


def random_game(rng, n, k, m, regular=False, loops=0):
    edges = []
    if regular:
        # a weighted cycle with a uniform weight plus a perfect-matching-free
        # second cycle: weighted degree is constant.
        for u in range(n):
            v = (u + 1) % n
            perm = list(range(k))
            rng.shuffle(perm)
            edges.append((u, v, 3, tuple(perm)))
        return edges
    for u in range(n):  # spanning path: no isolated vertices
        if u + 1 < n:
            perm = list(range(k))
            rng.shuffle(perm)
            edges.append((u, u + 1, rng.randint(1, 5), tuple(perm)))
    for _ in range(m):
        u, v = rng.sample(range(n), 2)
        perm = list(range(k))
        rng.shuffle(perm)
        edges.append((u, v, rng.randint(1, 5), tuple(perm)))
    for _ in range(loops):
        u = rng.randrange(n)
        perm = list(range(k))
        rng.shuffle(perm)
        edges.append((u, u, rng.randint(1, 40), tuple(perm)))
    return edges


def overlay(edges, n, k, c):
    W = sum(Fraction(w) for (_, _, w, _) in edges)
    deg = [Fraction(0)] * n
    for (u, v, w, _) in edges:
        deg[u] += w
        if v != u:
            deg[v] += w
    vol = sum(deg)
    new = [(u, v, Fraction(w), p) for (u, v, w, p) in edges]
    for u in range(n):
        for v in range(u + 1, n):
            wt = c * deg[u] * deg[v] / (vol * k)
            for a in range(k):
                new.append((u, v, wt, tuple((i + a) % k for i in range(k))))
    return new, W, deg


def val_of(edges, x):
    tot = sum(w for (_, _, w, _) in edges)
    sat = sum(w for (u, v, w, p) in edges if x[v] == p[x[u]])
    return Fraction(sat) / Fraction(tot)


def lambda2(edges, n):
    A = np.zeros((n, n))
    for (u, v, w, _) in edges:
        A[u, v] += float(w)
        if v != u:
            A[v, u] += float(w)
    d = A.sum(axis=1)
    Dm = np.diag(1.0 / np.sqrt(d))
    L = np.eye(n) - Dm @ A @ Dm
    ev = np.sort(np.linalg.eigvalsh(L))
    return ev[1]


def main():
    rng = random.Random(20260917)
    cs = [Fraction(1, 20), Fraction(1, 4), Fraction(1), Fraction(3)]
    fails = 0
    cases = 0
    below = 0
    for trial in range(180):
        n = rng.choice([3, 4, 5])
        k = rng.choice([2, 3])
        regular = trial % 4 == 0
        loops = 0 if (regular or trial % 3 == 0) else rng.randint(1, 3)
        edges = random_game(rng, n, k, rng.randint(0, 6), regular=regular,
                            loops=loops)
        labelings = list(itertools.product(range(k), repeat=n))
        vals = {x: val_of(edges, x) for x in labelings}
        valU = max(vals.values())
        if valU < Fraction(1, k):
            if loops == 0:
                fails += 1
                print("FAIL (D)", trial)
            else:
                below += 1
        for c in cs:
            cases += 1
            new, W, deg = overlay(edges, n, k, c)
            Omega = sum(w for (_, _, w, _) in new) - W
            if not (0 < Omega <= c * W):
                fails += 1
                print("FAIL Omega range", trial, c)
            if loops == 0 and 2 * max(deg) > sum(deg):
                fails += 1
                print("FAIL p_max", trial)
            best = Fraction(0)
            for x in labelings:
                vx = val_of(new, x)
                pred = (W * vals[x] + Omega / k) / (W + Omega)
                if vx != pred:
                    fails += 1
                    print("FAIL (A)", trial, c, x)
                best = max(best, vx)
            if not (valU / (1 + c) <= best <= max(valU, Fraction(1, k))):
                fails += 1
                print("FAIL (B)", trial, c, valU, best)
            lam = lambda2(new, n)
            cf = float(c)
            bound = cf * (1 + 2 * cf) / (1 + cf) ** 3
            if loops == 0:
                bound = max(bound, 3 * cf / (4 * (1 + cf)))
            if lam < bound - 1e-9:
                fails += 1
                print("FAIL (C)", trial, c, lam, bound)
            if regular and lam < float(c) / (1 + float(c)) - 1e-9:
                fails += 1
                print("FAIL (C-regular)", trial, c, lam)
    print(f"cases={cases} fails={fails} looped games with val < 1/k: {below}")
    print("ALL PASS" if fails == 0 else "FAILURES")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
