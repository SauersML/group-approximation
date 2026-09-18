#!/usr/bin/env python3
"""Death radius of metabelian-by-5-group quotients F_q^5 x| P of Pi_R(2,5).

P runs over 2-generated subgroups of A x| C5 in GL_5(F_q), q = 1 mod 5, with
A = {diag(z^v) : sum v = 0 mod 5} and C5 = <Y> (cyclic shift).  Every element
of A x| C5 has order dividing 5 (a product of the 5 conjugates of a sum-zero
diagonal is 1), so P has exponent 5; P = <a, b> with
    a = Y,  b = diag(z^e) Y^k,  e in F5^5 with sum e = 0, k in 0..4.
|P| = 5^(1 + dim F5[C5] e) for k = 0 (class = dim of the cyclic module).

For each (e, k) we solve the R-ball law system N_{rho(w)} c(w) = 0 in the
unknowns (c_a, c_b) in F_q^10 (see exponent_cohomology.py) and compare with
dim B = 5 - dim W^P.  We report the largest R with dim Z_R > dim B: at that
radius Pi_R(2,5) has the non-5-group quotient generated inside F_q^5 x| P.

Usage: python3 monomial_search.py q Rmax
"""
import sys
from itertools import product
import numpy as np


def rank_np(M, q):
    M = M.copy() % q
    rk = 0
    nrow, ncol = M.shape
    for col in range(ncol):
        if rk == nrow:
            break
        nz = np.nonzero(M[rk:, col])[0]
        if len(nz) == 0:
            continue
        p = rk + nz[0]
        M[[rk, p]] = M[[p, rk]]
        inv = pow(int(M[rk, col]), q - 2, q)
        M[rk] = (M[rk] * inv) % q
        f = M[:, col].copy()
        f[rk] = 0
        M = (M - np.outer(f, M[rk])) % q
        rk += 1
    return rk, M[:rk]


def zeta5(q):
    return next(x for x in range(2, q) if pow(x, 5, q) == 1)


def run(q, z, e, k, Rmax):
    d = 5
    I = np.eye(d, dtype=np.int64)
    Y = np.zeros((d, d), dtype=np.int64)
    for i in range(d):
        Y[i, (i + 1) % d] = 1
    D = np.diag([pow(z, int(x), q) for x in e]).astype(np.int64)
    ga = Y
    gb = (D @ np.linalg.matrix_power(Y, k)) % q
    mp = lambda M, n: np.linalg.matrix_power(M, n) % q if n else I
    gai, gbi = mp(ga, 4), mp(gb, 4)
    for g in (ga, gb):
        assert (mp(g, 5) == I).all()
    Z = np.zeros((d, d), dtype=np.int64)
    Ls = [np.hstack([I, Z]), np.hstack([(-gai) % q, Z]),
          np.hstack([Z, I]), np.hstack([Z, (-gbi) % q])]
    gs = [ga, gai, gb, gbi]
    # coboundaries and invariants
    B = np.vstack([(ga - I) % q, (gb - I) % q]).T  # row j = coboundary of e_j
    dimB, _ = rank_np(B, q)
    layer = [(-1, I, np.zeros((d, 2 * d), dtype=np.int64))]
    basis = np.zeros((0, 2 * d), dtype=np.int64)
    dims = []
    for R in range(1, Rmax + 1):
        new, rows = [], [basis]
        for last, g, L in layer:
            for s in range(4):
                if last >= 0 and last ^ 1 == s:
                    continue
                g2 = (g @ gs[s]) % q
                L2 = (L + g @ Ls[s]) % q
                N = (I + g2 + g2 @ g2 + mp(g2, 3) + mp(g2, 4)) % q
                rows.append((N @ L2) % q)
                new.append((s, g2, L2))
        layer = new
        rk, basis = rank_np(np.vstack(rows), q)
        dims.append(2 * d - rk)
        if 2 * d - rk == dimB:
            break
    return dimB, dims


def cyc_dim(e):
    """dim over F5 of the span of the cyclic shifts of e."""
    rows = [list(e[i:] + e[:i]) for i in range(5)]
    M = np.array(rows, dtype=np.int64)
    return rank_np(M, 5)[0]


def main():
    q, Rmax = int(sys.argv[1]), int(sys.argv[2])
    z = zeta5(q)
    seen = set()
    table = {}
    for e in product(range(5), repeat=5):
        if sum(e) % 5 or not any(e):
            continue
        # normalise up to shift and F5^* scaling
        cands = [tuple((s * x) % 5 for x in e[i:] + e[:i]) for i in range(5) for s in range(1, 5)]
        c = min(cands)
        for k in range(5):
            if (c, k) in seen:
                continue
            seen.add((c, k))
            dimB, dims = run(q, z, list(c), k, Rmax)
            last_alive = max([R for R, v in enumerate(dims, 1) if v > dimB], default=0)
            key = (cyc_dim(list(c)), k, dimB, last_alive)
            table.setdefault(key, []).append(c)
            print(f"e={c} k={k} cycdim={key[0]} dimB={dimB} dims={dims} last_alive_R={last_alive}")
            sys.stdout.flush()
    print("summary (cycdim, k, dimB, last R with a non-5-group quotient): count")
    for key in sorted(table):
        print("  ", key, len(table[key]))


if __name__ == "__main__":
    main()
