#!/usr/bin/env python3
"""Exponential brick compression in 2V: a length-(3d+1) word that is a product of
2^d pairwise-commuting, pairwise-disjoint-support baker maps.

Notation (matching research/brin-thompson-nv-max-type-size-functions-are-not-cnd):

    beta   : the global baker map of 2V,  (a s, t) |-> (s, a t).
    tau    : id x rho, where rho in V swaps the first two letters of the second
             coordinate, rho(a' a t) = a a' t.
    b_w    : the baker map supported on the brick [w] x C,
             (w a s, t) |-> (w s, a t), identity off [w] x C.
    B_d    : the product of the 2^d maps b_w over all binary words w of length d.
             The b_w have pairwise disjoint supports, so they commute and the product
             is independent of the order.

What is verified here, exactly (all group arithmetic is on strings; no floating point):

 1. b_w for |w| = d are pairwise disjoint-support, pairwise commuting elements of 2V,
    and their product is B_d.
 2. IDENTITY   B_d = (beta^{-1} tau)^d beta^{d+1}   as elements of 2V.
    Hence  |B_d| <= 3d + 1  in the two-element generating set {beta, tau}.
 3. RECURSION  beta B_d beta^{-1} = tau B_{d-1}   (the inductive form of 2).
 4. L(B_d) = 2^{d+1} exactly, where L is the minimal number of bricks in a brick
    diagram (lib2v.min_bricks, the exact guillotine DP).
    So log_2 L(B_d) = d + 1 >= (|B_d| - 1)/3: the minimal brick count is
    exponentially distorted with respect to word length in 2V.
 5. CONTRAST WITH V: for elements of V (embedded as V x id) the minimal brick count
    is subadditive, L(gh) <= L(g) + L(h) - 1, so L(g) <= C|g| and no such compression
    exists. Checked on random pairs of elements of V x id, and the multiplicative
    blow-up L(gh) ~ L(g) L(h) is exhibited on 2V pairs.
 6. The exponent cocycle of B_d is constant, c(B_d) = (-1, +1), so B_d has scale 1 and
    pattern depth 0: the compression is invisible to the cocycle statistics P1 and P2.

Usage:  python3 brick_compression.py [--dmax 8]
"""
import argparse
import os
import random
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "brin-thompson-cnd-2026-09-17"))

import lib2v  # noqa: E402
from lib2v import (ID, check, compose, inverse, is_identity, min_bricks,  # noqa: E402
                   reduce_greedy, v_on_x, v_on_y, word_element, random_word)

BETA = lib2v.BAKER                       # (a s, t) -> (s, a t)
RHO = [("00", "00"), ("01", "10"), ("10", "01"), ("11", "11")]   # a' a t -> a a' t
TAU = v_on_y(RHO)                        # id x rho


def words(d):
    if d == 0:
        return [""]
    out = [""]
    for _ in range(d):
        out = [w + a for w in out for a in "01"]
    return out


def baker_on(w):
    """b_w: (w a s, t) -> (w s, a t), identity off [w] x C."""
    bricks = [(w + a, "", w, a) for a in "01"]
    for i in range(len(w)):
        u = w[:i] + ("1" if w[i] == "0" else "0")
        bricks.append((u, "", u, ""))
    return tuple(sorted(bricks))


def B(d):
    """Product of b_w over all |w| = d, written down directly."""
    return tuple(sorted((w + a, "", w, a) for w in words(d) for a in "01"))


def power(g, k):
    if k < 0:
        return power(inverse(g), -k)
    out = ID
    for _ in range(k):
        out = reduce_greedy(compose(out, g))
    return out


def support_bricks(g):
    """Domain bricks on which g is not the identity."""
    return [b for b in g if (b[0], b[1]) != (b[2], b[3])]


def brick_overlap(b1, b2):
    def cmp(a, b):
        n = min(len(a), len(b))
        return a[:n] == b[:n]
    return cmp(b1[0], b2[0]) and cmp(b1[1], b2[1])


def disjoint_supports(g, h):
    return not any(brick_overlap(a, b) for a in support_bricks(g) for b in support_bricks(h))


def exponent_cocycle_values(g):
    """Set of (c_1, c_2) values of the exponent cocycle over the bricks of g."""
    return sorted({(len(rx) - len(dx), len(ry) - len(dy)) for (dx, dy, rx, ry) in g})


def T(d):
    """T_d in ker(exponent cocycle): flip letter d+1 of the first coordinate.

    T_d is a product of 2^d disjoint sibling swaps, lies in K_{d+1} = Sym(2^{2(d+1)}),
    and moves EVERY level-(d+1) cube.  T_d = beta^{-d} T_0 beta^d, so |T_d| <= 2d + 1.
    """
    return tuple(sorted((w + a, "", w + ("1" if a == "0" else "0"), "")
                        for w in words(d) for a in "01"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dmax", type=int, default=8)
    args = ap.parse_args()

    check(BETA)
    check(TAU)
    assert is_identity(compose(TAU, TAU)), "tau is an involution"
    assert min_bricks(BETA) == 2 and min_bricks(TAU) == 4

    binv_tau = reduce_greedy(compose(inverse(BETA), TAU))

    print("d  |  #pieces 2^d   L(B_d)   2^(d+1)   |B_d| <= 3d+1   c(B_d)")
    for d in range(0, args.dmax + 1):
        Bd = B(d)
        check(Bd)

        # ---- 1. B_d is the product of the 2^d disjoint-support baker maps b_w
        prod = ID
        bws = [baker_on(w) for w in words(d)]
        for bw in bws:
            check(bw)
            prod = reduce_greedy(compose(prod, bw))
        assert is_identity(compose(prod, inverse(Bd))), ("product != B_d", d)
        # disjointness and commutation, on a sample of pairs (all pairs for d <= 4)
        pairs = [(i, j) for i in range(len(bws)) for j in range(i + 1, len(bws))]
        rng = random.Random(7)
        if len(pairs) > 200:
            pairs = rng.sample(pairs, 200)
        for i, j in pairs:
            assert disjoint_supports(bws[i], bws[j]), ("supports meet", d, i, j)
            assert is_identity(compose(compose(bws[i], bws[j]),
                                       inverse(compose(bws[j], bws[i])))), ("no commute", d, i, j)

        # ---- 2. the closed form  B_d = (beta^{-1} tau)^d beta^{d+1}
        word = compose(power(binv_tau, d), power(BETA, d + 1))
        assert is_identity(compose(reduce_greedy(word), inverse(Bd))), ("closed form", d)

        # ---- 3. the recursion  beta B_d beta^{-1} = tau B_{d-1}
        if d >= 1:
            lhs = compose(compose(BETA, Bd), inverse(BETA))
            rhs = compose(TAU, B(d - 1))
            assert is_identity(compose(reduce_greedy(lhs), inverse(reduce_greedy(rhs)))), \
                ("recursion", d)

        # ---- 4. exact minimal brick count
        L = min_bricks(Bd)
        assert L == 2 ** (d + 1), ("L(B_d)", d, L)

        # ---- 6. exponent cocycle is constant
        coc = exponent_cocycle_values(Bd)
        assert coc == [(-1, 1)], ("cocycle", d, coc)

        print("%-2d |  %-12d %-8d %-9d %-15d %s"
              % (d, 2 ** d, L, 2 ** (d + 1), 3 * d + 1, coc))

    # ---- 7. the kernel family T_d = beta^{-d} T_0 beta^d (cocycle kernel, P3)
    T0 = v_on_x([("0", "1"), ("1", "0")])
    print("\nd  |  T_d in ker c   |T_d| <= 2d+1   level-(d+1) cubes moved   kernel depth")
    for d in range(0, args.dmax + 1):
        Td = T(d)
        check(Td)
        assert exponent_cocycle_values(Td) == [(0, 0)], ("T_d not in ker c", d)
        closed = compose(compose(power(BETA, -d), T0), power(BETA, d))
        assert is_identity(compose(reduce_greedy(closed), inverse(Td))), ("T_d closed form", d)
        # every level-(d+1) cube of C^2 is moved: the map flips letter d+1 of coordinate 1
        moved = 2 ** (2 * (d + 1))
        print("%-2d |  yes            %-14d %-24d %d" % (d, 2 * d + 1, moved, d + 1))

    # ---- 5a. V control: leaf count is subadditive under composition
    rng = random.Random(11)
    vletters = ["x0x", "x1x", "c0x", "c1x", "pix"]
    worst = 0.0
    for _ in range(300):
        g = word_element(random_word(rng.randint(1, 6), rng, vletters))
        h = word_element(random_word(rng.randint(1, 6), rng, vletters))
        gh = reduce_greedy(compose(g, h))
        Lg, Lh, Lgh = min_bricks(g), min_bricks(h), min_bricks(gh)
        assert Lgh <= Lg + Lh - 1, ("V subadditivity fails", Lg, Lh, Lgh)
        worst = max(worst, Lgh / float(Lg + Lh - 1))
    print("\nV x id control: L(gh) <= L(g)+L(h)-1 on 300 random pairs; "
          "worst ratio to the bound = %.3f" % worst)

    # ---- 5b. 2V: multiplicative blow-up of the brick count on one explicit pair
    #      a V-element in x with L = a bricks, and a V-element in y with L = b bricks,
    #      commute and their product needs a*b bricks.
    gx = v_on_x([("0", "00"), ("10", "01"), ("11", "1")])       # x0 in the x coordinate
    gy = v_on_y([("0", "00"), ("10", "01"), ("11", "1")])       # x0 in the y coordinate
    gp = reduce_greedy(compose(gx, gy))
    print("2V blow-up: L(x0 x id) = %d, L(id x x0) = %d, L(product) = %d (= 3*3)"
          % (min_bricks(gx), min_bricks(gy), min_bricks(gp)))
    assert min_bricks(gp) == min_bricks(gx) * min_bricks(gy)

    # ---- the ceiling this forces on any cnd function
    print("\nceiling: for every cnd psi on 2V with psi(e)=0, sqrt(psi) is subadditive, so")
    print("  psi(B_d) <= (3d+1)^2 * max(psi(beta), psi(tau))  while B_d has 2^d pieces.")
    print("  an aggregate  (sum over pieces of size^p)^(1/p) = 2^(d/p) is therefore")
    print("  capped: any psi >= F(aggregate) forces F(t) = O((log t)^2) for every p < oo.")
    print("\nall checks passed")


if __name__ == "__main__":
    main()
