#!/usr/bin/env python3
"""Abelian-by-5-group quotients of Pi_R(2,5): exponent cohomology.

Q = W x| P with P a finite 5-group, W an irreducible F_q P-module, q != 5.
A marking a -> (c_a, rho(pa)), b -> (c_b, rho(pb)) extends to a cocycle c on
F_2 (c(gh) = c(g) + g.c(h)).  (c(w), g)^5 = (N_g c(w), g^5) with
N_g = 1 + g + ... + g^4, so the R-ball law is the linear system
    N_{rho(w)} c(w) = 0   for all reduced words |w| <= R
in the unknowns (c_a, c_b) in W^2.  The solution space Z_R contains the
coboundaries B = {c_g = (g-1)v}; dim B = dim W when W^P = 0.  If dim Z_R >
dim B, some c is not a coboundary, the generated subgroup contains W, and
Pi_R(2,5) has the non-5-group quotient W x| P.

Cases: P = Z5^2 on a 1-dim character (dim W = 1), and P = H5 (Heisenberg,
order 125) on its 5-dim monomial representation, over F_q with q = 1 mod 5,
for every marking of P by a basis of P/Phi(P) = F5^2.

Usage: python3 exponent_cohomology.py q Rmax
"""
import sys
from itertools import product


def rank_mod(rows, q):
    rows = [list(r) for r in rows]
    rk, ncol = 0, len(rows[0]) if rows else 0
    for col in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][col] % q), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], q - 2, q)
        rows[rk] = [(x * inv) % q for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col] % q:
                f = rows[i][col]
                rows[i] = [(x - f * y) % q for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk, rows[:rk]


def mat_mul(A, B, q):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(len(B))) % q
                       for j in range(len(B[0]))) for i in range(len(A)))


def mat_add(A, B, q):
    return tuple(tuple((x + y) % q for x, y in zip(ra, rb)) for ra, rb in zip(A, B))


def ident(d):
    return tuple(tuple(int(i == j) for j in range(d)) for i in range(d))


def mat_pow(A, e, q):
    R = ident(len(A))
    for _ in range(e):
        R = mat_mul(R, A, q)
    return R


def norm5(g, q):
    d = len(g)
    N, P = ident(d), ident(d)
    for _ in range(4):
        P = mat_mul(P, g, q)
        N = mat_add(N, P, q)
    return N


def law_ranks(ga, gb, q, Rmax):
    """ranks of the R-ball law system, R = 1..Rmax; unknowns (c_a, c_b) in F_q^{2d}."""
    d = len(ga)
    I = ident(d)
    Z = tuple(tuple(0 for _ in range(d)) for _ in range(d))
    ga_inv = mat_pow(ga, 4, q)
    gb_inv = mat_pow(gb, 4, q)
    neg = lambda M: tuple(tuple((-x) % q for x in r) for r in M)
    # letter s: (rho(s), L_s as d x 2d)
    letters = [
        (ga, tuple(I[i] + Z[i] for i in range(d))),
        (ga_inv, tuple(neg(ga_inv)[i] + Z[i] for i in range(d))),
        (gb, tuple(Z[i] + I[i] for i in range(d))),
        (gb_inv, tuple(Z[i] + neg(gb_inv)[i] for i in range(d))),
    ]
    invl = [1, 0, 3, 2]
    layer = [(None, I, tuple(tuple(0 for _ in range(2 * d)) for _ in range(d)))]
    rows, ranks = [], []
    for R in range(1, Rmax + 1):
        new = []
        for last, g, L in layer:
            for s in range(4):
                if last is not None and invl[last] == s:
                    continue
                gs, Ls = letters[s]
                g2 = mat_mul(g, gs, q)
                L2 = mat_add(L, mat_mul(g, Ls, q), q)
                if mat_pow(g2, 5, q) != I:
                    raise ValueError("P not of exponent 5")
                rows.extend(mat_mul(norm5(g2, q), L2, q))
                new.append((s, g2, L2))
        layer = new
        rk, rows = rank_mod(rows, q)  # keep only an echelon basis
        ranks.append(rk)
    return ranks


def zeta5(q):
    for x in range(2, q):
        if pow(x, 5, q) == 1:
            return x
    raise ValueError("q != 1 mod 5")


def bases():
    vecs = [v for v in product(range(5), repeat=2) if v != (0, 0)]
    return [(u, v) for u in vecs for v in vecs if (u[0] * v[1] - u[1] * v[0]) % 5]


def main():
    q, Rmax = int(sys.argv[1]), int(sys.argv[2])
    only_std = len(sys.argv) > 3  # only the marking a -> X, b -> Y for H5
    z = zeta5(q)
    # 1-dim characters of Z5^2: a -> z^i, b -> z^j, (i,j) != (0,0)
    hist = {}
    for i, j in product(range(5), repeat=2):
        if (i, j) == (0, 0):
            continue
        ranks = law_ranks(((pow(z, i, q),),), ((pow(z, j, q),),), q, Rmax)
        sol = [2 - r for r in ranks]
        hist.setdefault(tuple(sol), []).append((i, j))
    print(f"q={q} P=Z5^2, dim W=1, dim B=1; solution dims per R=1..{Rmax}:")
    for k, v in sorted(hist.items()):
        print(f"   {list(k)}: {len(v)} characters, e.g. {v[:4]}")
    X = tuple(tuple(pow(z, i, q) if i == j else 0 for j in range(5)) for i in range(5))
    Y = tuple(tuple(1 if j == (i + 1) % 5 else 0 for j in range(5)) for i in range(5))
    hist = {}
    for (i1, j1), (i2, j2) in ([((1, 0), (0, 1))] if only_std else bases()):
        ga = mat_mul(mat_pow(X, i1, q), mat_pow(Y, j1, q), q)
        gb = mat_mul(mat_pow(X, i2, q), mat_pow(Y, j2, q), q)
        ranks = law_ranks(ga, gb, q, Rmax)
        sol = [10 - r for r in ranks]
        hist.setdefault(tuple(sol), []).append(((i1, j1), (i2, j2)))
    print(f"q={q} P=H5, dim W=5, dim B=5; solution dims per R=1..{Rmax}:")
    for k, v in sorted(hist.items()):
        print(f"   {list(k)}: {len(v)} markings, e.g. {v[:2]}")


if __name__ == "__main__":
    main()
