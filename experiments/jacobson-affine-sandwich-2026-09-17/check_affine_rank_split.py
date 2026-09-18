#!/usr/bin/env python3
"""Finite check of the affine rank split (claim jacobson-haar-character-restricts-to-orbit-relation-summand).

In A_k = F_2^k x| GL_k(F_2), acting on F_2^(k+1) by h(v,g)(x, y) = (g x + y v, y), check:
  (R)   rank(h - 1) = rank(g - 1) + [v notin Im(g - 1)];
  (AS1) 2^(-m rank(h-1)) = (1 - 2^-m) psi_m(v,g) + 2^-m 2^(-m rank(g-1)),  m = 1, 2, 3,
        psi_m(v,g) = 2^(-m rank(g-1)) [v in Im(g-1)];
  (3.1) psi_1(v,g) = 2^-k * sum over xi in Fix(g) of (-1)^(xi.v), where Fix(g) = {xi : xi o g^-1 = xi};
  (PSD) the matrices psi_m(a^-1 b), m = 1, 2, are positive semidefinite (k = 2 and k = 3).
Run: python3 check_affine_rank_split.py
"""
import itertools
import numpy as np


def rank2(rows, ncols):
    """Rank over F_2 of a list of integer bitmask rows."""
    rows = [r for r in rows if r]
    rank = 0
    for bit in range(ncols):
        piv = next((i for i, r in enumerate(rows) if (r >> bit) & 1), None)
        if piv is None:
            continue
        p = rows.pop(piv)
        rows = [r ^ p if (r >> bit) & 1 else r for r in rows]
        rank += 1
    return rank


def mat_vec(M, x, k):
    """M is a tuple of k columns (bitmasks); return M x."""
    out = 0
    for j in range(k):
        if (x >> j) & 1:
            out ^= M[j]
    return out


def gl(k):
    cols = range(1, 2 ** k)
    for M in itertools.product(cols, repeat=k):
        if rank2(list(M), k) == k:
            yield M


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return s


def main():
    for k in (1, 2, 3):
        G = list(gl(k))
        V = range(2 ** k)
        elems = []
        for g in G:
            gm1 = tuple(g[j] ^ (1 << j) for j in range(k))
            r = rank2(list(gm1), k)
            im = span(gm1)
            ginv = {mat_vec(g, x, k): x for x in V}
            for v in V:
                # h - 1 on F_2^(k+1): columns (g - 1)e_j for j < k, and v for the last basis vector.
                rh = rank2(list(gm1) + [v], k)
                assert rh == r + (v not in im), (k, g, v)
                for m in (1, 2, 3):
                    psi = 2.0 ** (-m * r) * (v in im)
                    lhs = 2.0 ** (-m * rh)
                    rhs = (1 - 2.0 ** -m) * psi + 2.0 ** -m * 2.0 ** (-m * r)
                    assert abs(lhs - rhs) < 1e-12
                # (3.1): xi in dual = F_2^k via xi(x) = popcount(xi & x) mod 2; (g.xi)(x) = xi(g^-1 x)
                tot = 0
                for xi in V:
                    if all(bin(xi & ginv[x]).count("1") % 2 == bin(xi & x).count("1") % 2 for x in V):
                        tot += (-1) ** (bin(xi & v).count("1") % 2)
                assert abs(tot / 2 ** k - 2.0 ** -r * (v in im)) < 1e-12
                elems.append((v, g, r, im))
        print(f"k={k}: |A_k|={len(elems)}  rank formula, (AS1) m=1..3 and (3.1) verified")
        if k >= 2:
            ginv_of = {}
            for g in G:
                ginv_of[g] = tuple(
                    next(x for x in V if mat_vec(g, x, k) == (1 << j)) for j in range(k)
                )
            idx = {(v, g): i for i, (v, g, _, _) in enumerate(elems)}
            data = {(v, g): (r, im) for (v, g, r, im) in elems}

            def mul(a, b):
                (v, g), (w, h) = a, b
                gh = tuple(mat_vec(g, h[j], k) for j in range(k))
                return (v ^ mat_vec(g, w, k), gh)

            def inv(a):
                v, g = a
                gi = ginv_of[g]
                return (mat_vec(gi, v, k), gi)

            keys = [(v, g) for (v, g, _, _) in elems]
            inverses = [inv(a) for a in keys]
            for m in (1, 2):
                P = np.empty((len(keys), len(keys)))
                for i, a in enumerate(keys):
                    ai = inverses[i]
                    for j, b in enumerate(keys):
                        r, im = data[mul(ai, b)]
                        c = mul(ai, b)
                        P[i, j] = 2.0 ** (-m * r) * (c[0] in im)
                lam = np.linalg.eigvalsh(P).min()
                assert lam > -1e-9, (k, m, lam)
                print(f"k={k}: psi_{m} positive semidefinite (min eigenvalue {lam:.3e})")
    print("all checks passed")


if __name__ == "__main__":
    main()
