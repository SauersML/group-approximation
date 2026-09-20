"""Checks for fpbs-cs-barrier-hypothesis-fails-finite-free-capacity-normal.

A finite set Y is *free* if for every k, distinct length-k sequences from Y
(repetitions allowed) have distinct products. b(Kt) is the largest size of a
free subset of the coset Kt. The proof bounds b(Kt); this script checks the
bounds and the calibration on concrete examples. Exact integer/rational
arithmetic only.

1. K = Z^2, t acting by M = [[2,1],[1,1]] (Z^2 x|_M Z, and so Z^2 x| F_2 with
   a hyperbolic generator). Products of v_i t are
   (v_{i1} + M v_{i2} + ... + M^{k-1} v_{ik}) t^k.  The proof gives b = 2:
   pairs are free (height-one polynomials have no root > 2, and the golden
   square 2.618 is > 2), triples are not (3 > 2.618 = Mahler measure).
2. K = Z^2, t acting trivially: b = 1 (pairs collide at k = 2).
3. K = Heisenberg, t trivial (the direct-product case K x H): pairs of
   distinct elements collide at some length (polynomial growth).
4. Calibration: in BS(1,2) the affine maps x: z -> 2z, y: z -> 2z+1 generate a
   free semigroup, and U_n = {x y^i : i < n} is free of size n, so b = infinity
   when K contains a free subsemigroup.
"""
from fractions import Fraction
from itertools import product

M = ((2, 1), (1, 1))


def mat_vec(A, v):
    return (A[0][0] * v[0] + A[0][1] * v[1], A[1][0] * v[0] + A[1][1] * v[1])


def mat_mul(A, B):
    return tuple(tuple(sum(A[i][l] * B[l][j] for l in range(2)) for j in range(2))
                 for i in range(2))


def twisted_parts(vs, k, A):
    """Map each length-k index sequence to v_{i1} + A v_{i2} + ... + A^{k-1} v_{ik}."""
    powers = [((1, 0), (0, 1))]
    for _ in range(k - 1):
        powers.append(mat_mul(A, powers[-1]))
    img = [[mat_vec(P, v) for v in vs] for P in powers]
    out = {}
    for seq in product(range(len(vs)), repeat=k):
        x = y = 0
        for j, i in enumerate(seq):
            x += img[j][i][0]
            y += img[j][i][1]
        out.setdefault((x, y), []).append(seq)
    return out


def first_collision(vs, kmax, A):
    for k in range(1, kmax + 1):
        parts = twisted_parts(vs, k, A)
        for key, seqs in parts.items():
            if len(seqs) > 1:
                return k, seqs[0], seqs[1], len(parts), len(vs) ** k
    return None


def check_hyperbolic():
    print("== 1. Z^2 twisted by M = [[2,1],[1,1]] ==")
    pairs = [[(0, 0), (1, 0)], [(0, 0), (0, 1)], [(0, 0), (1, -1)],
             [(0, 0), (2, 3)], [(1, 2), (-3, 1)]]
    for vs in pairs:
        res = first_collision(vs, 16, M)
        print("pair", vs, "free through k=16" if res is None else ("COLLISION", res))
        assert res is None
    triples = [[(0, 0), (1, 0), (0, 1)], [(0, 0), (1, 0), (2, 0)],
               [(0, 0), (1, 0), (-1, 0)], [(0, 0), (1, 1), (5, -2)]]
    for vs in triples:
        res = first_collision(vs, 12, M)
        print("triple", vs, "->", res if res is None else
              "collision at k=%d: %s vs %s; distinct parts %d of %d" % res)
        assert res is not None
    # growth of distinct K-parts for all 3^k sequences vs the bound C * 2.618^k
    vs = [(0, 0), (1, 0), (0, 1)]
    for k in range(1, 11):
        n = len(twisted_parts(vs, k, M))
        print("  k=%2d  #distinct parts=%6d  3^k=%6d  ratio to 2.618^k=%.2f"
              % (k, n, 3 ** k, n / 2.6180339887 ** k))


def check_trivial_twist():
    print("== 2. Z^2, t central ==")
    I = ((1, 0), (0, 1))
    res = first_collision([(0, 0), (1, 0)], 4, I)
    print("pair collision:", res)
    assert res is not None and res[0] == 2


def heis_mul(g, h):
    a, b, c = g
    x, y, z = h
    return (a + x, b + y, c + z + a * y)


def check_heisenberg():
    print("== 3. Heisenberg, t central ==")
    pairs = [((1, 0, 0), (0, 1, 0)), ((1, 0, 0), (1, 1, 0)),
             ((2, 1, 0), (1, 3, 5)), ((1, 0, 0), (0, 0, 1))]
    for u in pairs:
        found = None
        for k in range(1, 12):
            seen = {}
            for seq in product(range(2), repeat=k):
                g = (0, 0, 0)
                for i in seq:
                    g = heis_mul(g, u[i])
                if g in seen:
                    found = (k, seen[g], seq)
                    break
                seen[g] = seq
            if found:
                break
        print("pair", u, "first collision", found)
        assert found is not None


def aff_mul(f, g):
    # affine maps z -> p z + q stored as (p, q); (f*g)(z) = f(g(z))
    return (f[0] * g[0], f[0] * g[1] + f[1])


def check_calibration():
    print("== 4. BS(1,2) calibration: U_n = {x y^i} ==")
    x = (Fraction(2), Fraction(0))
    y = (Fraction(2), Fraction(1))
    for n in range(2, 6):
        U = []
        for i in range(n):
            g = x
            for _ in range(i):
                g = aff_mul(g, y)
            U.append(g)
        for k in range(1, 6 if n <= 3 else 4):
            vals = set()
            for seq in product(range(n), repeat=k):
                g = (Fraction(1), Fraction(0))
                for i in seq:
                    g = aff_mul(g, U[i])
                vals.add(g)
            assert len(vals) == n ** k, (n, k)
        print("U_%d free through the tested lengths" % n)


if __name__ == "__main__":
    check_hyperbolic()
    check_trivial_twist()
    check_heisenberg()
    check_calibration()
    print("ALL CHECKS PASSED")
