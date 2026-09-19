#!/usr/bin/env python3
"""Check the periodic models used in bilateral-laurent-haar-relation-is-sofic.

G = A^n x| SL_n(A), A = F_2[z, z^-1], acts on X = (F_2^Z)^n by x -> g x + w.
The m-periodic points form (A/(z^m - 1))^n = F_2^(m x n), and G acts on them
through A -> A_m = A/(z^m - 1).  This script checks, for random words g:

  (P1) the periodic action is an action: (g h) acting equals g after h;
  (P2) Fix_m(g) has proportion <= 2^-(m - spread(g - 1)) when the linear
       part of g is not 1, where spread is the largest span of an entry
       (the bound used in the proof);
  (P3) for gamma = 1 and w != 0, Fix_m is empty once m exceeds the span of w;
  (P4) exact covariance on cylinders: (g x)|window depends only on x on the
       window enlarged by the propagation radius, and agrees with the
       bilateral action, once m is larger than the enlarged window.

Laurent polynomials are dicts {exponent: 1} over F_2 (sets of exponents).
"""
import random
import itertools

random.seed(20260917)


def padd(a, b):
    return a ^ b  # frozenset symmetric difference


def pmul(a, b):
    out = set()
    for i in a:
        for j in b:
            out ^= {i + j}
    return frozenset(out)


def matmul(M, N, n):
    return [[frozenset().union() if False else
             _sum([pmul(M[i][k], N[k][j]) for k in range(n)])
             for j in range(n)] for i in range(n)]


def _sum(ps):
    out = frozenset()
    for p in ps:
        out = out ^ p
    return out


def ident(n):
    return [[frozenset({0}) if i == j else frozenset() for j in range(n)] for i in range(n)]


def elem(n, i, j, a):
    M = ident(n)
    M[i][j] = a
    return M


def rand_poly(r=2):
    s = frozenset(e for e in range(-r, r + 1) if random.random() < 0.4)
    return s if s else frozenset({random.randint(-r, r)})


def rand_word(n, length=3):
    M = ident(n)
    for _ in range(length):
        i, j = random.sample(range(n), 2)
        M = matmul(M, elem(n, i, j, rand_poly()), n)
    return M


def apply_periodic(M, w, x, n, m):
    """x: list of n lists of length m over F_2 (index k = coefficient of z^k mod m)."""
    y = [[0] * m for _ in range(n)]
    for i in range(n):
        for j in range(n):
            for e in M[i][j]:
                for k in range(m):
                    if x[j][k]:
                        y[i][(k + e) % m] ^= 1
    for i in range(n):
        for e in w[i]:
            y[i][e % m] ^= 1
    return y


def rank_f2(rows):
    rows = [int("".join(map(str, r)), 2) for r in rows]
    rank = 0
    while rows:
        piv = max(rows)
        if piv == 0:
            break
        rows.remove(piv)
        top = piv.bit_length() - 1
        rows = [r ^ piv if (r >> top) & 1 else r for r in rows]
        rank += 1
    return rank


def linear_matrix(M, n, m):
    """Matrix of x -> (M - 1) x on F_2^(n m) (rows = output coords)."""
    cols = []
    for j in range(n):
        for k in range(m):
            x = [[0] * m for _ in range(n)]
            x[j][k] = 1
            y = apply_periodic(M, [frozenset()] * n, x, n, m)
            y[j][k] ^= 1
            cols.append([y[i][t] for i in range(n) for t in range(m)])
    return [list(r) for r in zip(*cols)]


def spread(M, n):
    s = 0
    for i in range(n):
        for j in range(n):
            p = M[i][j] ^ (frozenset({0}) if i == j else frozenset())
            if p:
                s = max(s, max(p) - min(p))
    return s


def is_identity(M, n):
    return all(M[i][j] == (frozenset({0}) if i == j else frozenset()) for i in range(n) for j in range(n))


def main():
    n = 3
    fails = 0
    checks = 0
    # (P1) action property
    for _ in range(20):
        m = random.randint(4, 9)
        g, h = rand_word(n), rand_word(n)
        wg = [rand_poly() for _ in range(n)]
        wh = [rand_poly() for _ in range(n)]
        # (w_g, g)(w_h, h) = (w_g + g w_h, g h)
        gwh = [_sum([pmul(g[i][j], wh[j]) for j in range(n)]) for i in range(n)]
        wgh = [padd(wg[i], gwh[i]) for i in range(n)]
        gh = matmul(g, h, n)
        x = [[random.randint(0, 1) for _ in range(m)] for _ in range(n)]
        lhs = apply_periodic(gh, wgh, x, n, m)
        rhs = apply_periodic(g, wg, apply_periodic(h, wh, x, n, m), n, m)
        checks += 1
        fails += lhs != rhs
    print("P1 action property: %d checks, %d failures" % (checks, fails))

    # (P2) fixed-point proportion bound for nontrivial linear part
    worst = 0
    tested = 0
    for _ in range(40):
        g = rand_word(n)
        if is_identity(g, n):
            continue
        s = spread(g, n)
        for m in range(s + 2, s + 9):
            r = rank_f2(linear_matrix(g, n, m))
            tested += 1
            if r < m - s:
                worst += 1
    print("P2 rank(gamma-1 mod z^m-1) >= m - spread: %d cases, %d violations" % (tested, worst))

    # (P3) pure translations have no periodic fixed points once m > span(w)
    bad = 0
    for _ in range(40):
        w = [rand_poly(3) for _ in range(n)]
        span = max(max(p) - min(p) for p in w if p)
        m = span + 1
        wm = [[0] * m for _ in range(n)]
        for i in range(n):
            for e in w[i]:
                wm[i][e % m] ^= 1
        bad += all(v == 0 for row in wm for v in row)
    print("P3 translation reduction nonzero for m > span: 40 cases, %d failures" % bad)

    # (P4) window covariance: compare periodic action with bilateral action on a window
    bad = 0
    for _ in range(20):
        g = rand_word(n, 2)
        w = [rand_poly() for _ in range(n)]
        r = max([abs(e) for i in range(n) for j in range(n) for e in g[i][j]] + [0])
        wr = max([abs(e) for p in w for e in p] + [0])
        a = 3  # window [-a, a]
        R = a + r
        m = 2 * max(R, wr) + 2 * a + 3
        # random bilateral x on [-R-1, R+1], zero-agnostic: test that output on the window
        # depends only on x on [-R, R] and matches the periodic computation
        xb = {(j, k): random.randint(0, 1) for j in range(n) for k in range(-R, R + 1)}
        yb = {}
        for i in range(n):
            for k in range(-a, a + 1):
                v = 0
                for j in range(n):
                    for e in g[i][j]:
                        v ^= xb[(j, k - e)]
                v ^= int(k in w[i])
                yb[(i, k)] = v
        xp = [[0] * m for _ in range(n)]
        for (j, k), v in xb.items():
            xp[j][k % m] = v
        # fill the rest of the period randomly: must not affect the window
        for j in range(n):
            for k in range(m):
                kk = k if k <= m // 2 else k - m
                if abs(kk) > R:
                    xp[j][k] = random.randint(0, 1)
        yp = apply_periodic(g, w, xp, n, m)
        for i in range(n):
            for k in range(-a, a + 1):
                bad += yp[i][k % m] != yb[(i, k)]
    print("P4 window covariance mismatches: %d" % bad)


if __name__ == "__main__":
    main()
