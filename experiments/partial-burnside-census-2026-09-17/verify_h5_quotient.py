#!/usr/bin/env python3
"""Independent check: an explicit non-5-group quotient F_q^5 x| H5 of Pi_R(2,5).

Finds (c_a, c_b) solving the R-ball law system of exponent_cohomology.py that
is not a coboundary, then verifies DIRECTLY, by composing affine maps
v -> g v + c of F_q^5, that h^5 = 1 for every reduced word h with |h| <= R,
and exhibits a word of length R+1 whose fifth power is a nonzero translation.
Since W = F_q^5 is irreducible for H5 and c is not a coboundary, the group
generated contains W, so it is F_q^5 x| H5 of order q^5 * 125.

Usage: python3 verify_h5_quotient.py q R
"""
import sys
from itertools import product
from exponent_cohomology import mat_mul, mat_add, mat_pow, ident, norm5, zeta5


def nullspace(rows, ncol, q):
    rows = [list(r) for r in rows]
    piv_cols, rk = [], 0
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
        piv_cols.append(col)
        rk += 1
    free = [c for c in range(ncol) if c not in piv_cols]
    basis = []
    for fc in free:
        v = [0] * ncol
        v[fc] = 1
        for i, pc in enumerate(piv_cols):
            v[pc] = (-rows[i][fc]) % q
        basis.append(v)
    return basis, rk


def main():
    q, R = int(sys.argv[1]), int(sys.argv[2])
    z = zeta5(q)
    d = 5
    X = tuple(tuple(pow(z, i, q) if i == j else 0 for j in range(d)) for i in range(d))
    Y = tuple(tuple(1 if j == (i + 1) % d else 0 for j in range(d)) for i in range(d))
    I = ident(d)
    words = [()]
    frontier = [()]
    for L in range(R + 1):
        nf = []
        for w in frontier:
            for s in range(4):
                if w and w[-1] ^ 1 == s:
                    continue
                nf.append(w + (s,))
        words += nf
        frontier = nf
    words = [w for w in words if w]
    # symbolic cocycle rows
    gens = [X, mat_pow(X, 4, q), Y, mat_pow(Y, 4, q)]

    def rho_L(w):
        g = I
        L = [[0] * (2 * d) for _ in range(d)]
        for s in w:
            gs = gens[s]
            # c(g s) = c(g) + g c(s); c(a) = e_a, c(a^-1) = -a^-1 c(a)
            Ls = [[0] * (2 * d) for _ in range(d)]
            off = 0 if s < 2 else d
            M = I if s % 2 == 0 else tuple(tuple((-x) % q for x in r) for r in gs)
            for i in range(d):
                for j in range(d):
                    Ls[i][off + j] = M[i][j]
            GL = mat_mul(g, Ls, q)
            L = [[(L[i][j] + GL[i][j]) % q for j in range(2 * d)] for i in range(d)]
            g = mat_mul(g, gs, q)
        return g, L

    rows = []
    for w in words:
        if len(w) <= R:
            g, L = rho_L(w)
            rows.extend(mat_mul(norm5(g, q), L, q))
    sol, rk = nullspace(rows, 2 * d, q)
    # coboundaries: c_a = (X - 1) v, c_b = (Y - 1) v
    cob = []
    for k in range(d):
        v = [int(i == k) for i in range(d)]
        ca = [(sum(X[i][j] * v[j] for j in range(d)) - v[i]) % q for i in range(d)]
        cb = [(sum(Y[i][j] * v[j] for j in range(d)) - v[i]) % q for i in range(d)]
        cob.append(ca + cb)
    _, rkB = nullspace(cob, 2 * d, q)
    print(f"q={q} R={R}: dim Z_R = {len(sol)}, dim B = {rkB}")
    chosen = None
    for v in sol:
        _, r2 = nullspace(cob + [v], 2 * d, q)
        if r2 > rkB:
            chosen = v
            break
    if chosen is None:
        print("no non-coboundary solution")
        return
    ca, cb = chosen[:d], chosen[d:]
    print("c_a =", ca, "c_b =", cb)
    # direct affine check
    inv_aff = lambda A: None
    Xi, Yi = mat_pow(X, 4, q), mat_pow(Y, 4, q)
    neg = lambda v: [(-x) % q for x in v]
    ap = lambda M, v: [sum(M[i][j] * v[j] for j in range(d)) % q for i in range(d)]
    aff = [(X, ca), (Xi, neg(ap(Xi, ca))), (Y, cb), (Yi, neg(ap(Yi, cb)))]

    def compose(A, B):  # A then... as group product (g1,c1)(g2,c2) = (g1 g2, c1 + g1 c2)
        return (mat_mul(A[0], B[0], q), [(x + y) % q for x, y in zip(A[1], ap(A[0], B[1]))])

    bad_at = None
    for w in words:
        e = (I, [0] * d)
        for s in w:
            e = compose(e, aff[s])
        p = e
        for _ in range(4):
            p = compose(p, e)
        if p != (I, [0] * d):
            if len(w) <= R:
                print("LAW FAILS at", w)
                return
            if bad_at is None:
                bad_at = w
    print(f"verified: h^5 = 1 for all {sum(1 for w in words if len(w) <= R)} reduced words of length <= {R}")
    print("first failing word of length", R + 1, ":", bad_at)


if __name__ == "__main__":
    main()
