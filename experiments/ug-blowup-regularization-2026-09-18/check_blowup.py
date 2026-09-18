#!/usr/bin/env python3
"""Check the degree blow-up regularization of loop-free weighted unique games.

For random loop-free unique games U with integer multiplicities (half of them
bipartite, including orientation lifts of random 2-to-1 games), build B(U):
vertex u -> m_u = deg(u) copies, constraint e=(u,v,pi) -> every copy pair
(u_i, v_j) with weight w_e/(m_u m_v) and the same permutation.  Assert exactly
(Fractions):
  (a) B(U) is loop-free and weighted-regular (every copy has weighted degree 1);
  (b) the normalized-Laplacian spectrum of B(U) is spec(U) plus eigenvalue 1
      with multiplicity sum(m_u - 1), so lambda_2(B) = min(lambda_2(U), 1);
  (c) opt(B(U)) = opt(U) by brute force, and the random-copy average of the
      best B-labelling equals its value.
"""
import itertools
import random
from fractions import Fraction

import numpy as np


def norm_lap(n, edges):
    A = np.zeros((n, n))
    for (u, v, w, _) in edges:
        A[u, v] += float(w)
        A[v, u] += float(w)
    d = A.sum(1)
    Dm = np.diag(1 / np.sqrt(d))
    return np.eye(n) - Dm @ A @ Dm


def value(edges, lab):
    tot = sum(w for (_, _, w, _) in edges)
    sat = sum(w for (u, v, w, p) in edges if p[lab[u]] == lab[v])
    return Fraction(sat) / tot


def opt(n, k, edges):
    return max(value(edges, lab) for lab in itertools.product(range(k), repeat=n))


def blowup(n, edges):
    deg = [0] * n
    for (u, v, w, _) in edges:
        deg[u] += w
        deg[v] += w
    idx, start = [], 0
    for u in range(n):
        idx.append(list(range(start, start + deg[u])))
        start += deg[u]
    bed = []
    for (u, v, w, p) in edges:
        for i in idx[u]:
            for j in idx[v]:
                bed.append((i, j, Fraction(w, deg[u] * deg[v]), p))
    return start, bed, deg, idx


def random_game(rng, k, bipartite):
    if bipartite:
        a, b = rng.randint(1, 2), rng.randint(1, 2)
        n = a + b
        pairs = [(u, a + v) for u in range(a) for v in range(b)]
    else:
        n = rng.randint(2, 4)
        pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
    edges = []
    for (u, v) in pairs:
        for _ in range(rng.randint(0, 2)):
            p = list(range(k))
            rng.shuffle(p)
            edges.append((u, v, rng.randint(1, 2), tuple(p)))
    used = {x for e in edges for x in e[:2]}
    if len(used) < n or not edges:
        return None
    return n, edges


def lift_of_random_2to1(rng):
    # left alphabet [4], right alphabet [2]; lift right alphabet [2]x{0,1} = [4]
    a, b = 1, 2
    n = a + b
    edges = []
    for u in range(a):
        for v in range(b):
            p = [0, 0, 1, 1]
            rng.shuffle(p)
            o = [None] * 4
            for r in (0, 1):
                fib = [x for x in range(4) if p[x] == r]
                bit = rng.randint(0, 1)
                o[fib[0]], o[fib[1]] = bit, 1 - bit
            perm = tuple(2 * p[x] + o[x] for x in range(4))
            edges.append((u, a + v, rng.randint(1, 2), perm))
    return n, edges


def main():
    rng = random.Random(20260918)
    trials = 0
    while trials < 40:
        if trials % 4 == 3:
            g, k = lift_of_random_2to1(rng), 4
        else:
            k = 2 if trials % 2 else 3
            g = random_game(rng, k, bipartite=(trials % 4 == 1))
        if g is None:
            continue
        n, edges = g
        N, bed, deg, idx = blowup(n, edges)
        # (a) loop-free, regular
        assert all(i != j for (i, j, _, _) in bed)
        bdeg = [Fraction(0)] * N
        for (i, j, w, _) in bed:
            bdeg[i] += w
            bdeg[j] += w
        assert all(x == 1 for x in bdeg), bdeg
        # (b) spectrum
        s_u = sorted(np.linalg.eigvalsh(norm_lap(n, edges)))
        s_b = sorted(np.linalg.eigvalsh(norm_lap(N, bed)))
        extra = sum(m - 1 for m in deg)
        pred = sorted(list(s_u) + [1.0] * extra)
        assert np.allclose(s_b, pred, atol=1e-8), (s_b, pred)
        lam_u, lam_b = s_u[1], s_b[1]
        assert abs(lam_b - (min(lam_u, 1.0) if extra else lam_u)) < 1e-8
        # (c) opt equality (brute force over B only when small)
        ou = opt(n, k, edges)
        if N <= 7:
            ob = opt(N, k, bed)
            assert ob == ou, (ob, ou)
            best = max(itertools.product(range(k), repeat=N),
                       key=lambda lab: value(bed, lab))
            avg = Fraction(0)
            choices = list(itertools.product(*idx))
            for ch in choices:
                avg += value(edges, [best[c] for c in ch])
            avg /= len(choices)
            assert avg == value(bed, best)
        # lifted labelling has equal value
        lab = [rng.randrange(k) for _ in range(n)]
        blab = [None] * N
        for u in range(n):
            for i in idx[u]:
                blab[i] = lab[u]
        assert value(bed, blab) == value(edges, lab)
        trials += 1
        print(f"trial {trials:2d}: n={n} N={N} k={k} lam2(U)={lam_u:.4f} "
              f"lam2(B)={lam_b:.4f} opt={ou}")
    print("ALL 40 TRIALS PASS")


if __name__ == "__main__":
    main()
