#!/usr/bin/env python3
"""Audit computations for `rich-2to1-hard-at-completeness-one-half` (2026-09-18).

Two independent checks, both with exact rational arithmetic.

(A) The *generic* reading of Khot--Minzer--Safra footnote 2 -- "the constraints
    are easily reinterpreted as being 2-to-1 constraints" -- is quantitatively
    false if one reads it as a gap-preserving transformation of a linear
    2-to-2 game into a bipartite 2-to-1 game.

    Let `U` be an instance of `2-to-2 Game[F_2^l]` with constraints
    `T_c x_i + T'_c x_j in {b_c, b'_c}`, `b_c != b'_c`, of weight `w_c`.
    Put `d_c = b_c + b'_c` and `H_c = {0, d_c}`, and let `q_c` be the quotient
    map `F_2^l -> F_2^l / H_c`, which is exactly 2-to-1 onto a set of size
    `2^(l-1)`. The constraint says exactly `q_c(T_c x_i + b_c) = q_c(T'_c x_j)`.
    Build the bipartite game `B(U)`: left vertices are the variables with
    alphabet `F_2^l` (size `2k`, `k = 2^(l-1)`), right vertices are the
    constraints with alphabet `F_2^l / H_c` (size `k`), and constraint `c`
    contributes the two edges

        (x_i, c) with the 2-to-1 map  a -> q_c(T_c a + b_c),
        (x_j, c) with the 2-to-1 map  a -> q_c(T'_c a),

    each of weight `w_c / 2`. Every edge map is exactly 2-to-1, so `B(U)` is a
    2-to-1 game in the sense of Dinur--Khot--Kindler--Minzer--Safra
    Definition 1.2, and `B` is the only shape of bipartization that keeps the
    alphabet sizes `(2k, k)` and puts one fresh right vertex per constraint.

    CHECK: `val(B(U)) = (1 + OPT(U)) / 2` exactly, for every instance.

    Consequence: `B` maps `Gap 2-to-2[1-eps, eps]` to
    `Gap 2-to-1[1 - eps/2, (1+eps)/2]`. Its soundness is above one half, so it
    never yields `Gap-2-to-1[1-eps, eps]`. Any route that needs the 2-to-1 form
    of the 2-to-2 Games Theorem must take it from DKKMS TR16-198 Theorem 1.2
    (whose Grassmann game is natively 2-to-1), not from a generic
    reinterpretation of the linear 2-to-2 constraints.

(B) Item (3) of `orientation-lifts-sandwich-2to1-game-values` is stated on the
    claim node as `val(U_o) = max_L sum_v max_b w_v(L, b)`, where `w_v(L, b)` is
    "the weight of edges e = (u,v) that L satisfies in G, with the best right
    label, and whose branch is o_e(L_u) = b". Read literally (the G-optimal
    right label `m*` first, then the split by branch), the identity is FALSE:
    it can strictly undercount. The derivation file fixes the reading ("uses
    the best `m` for the branch", i.e. `w_v(L,b) = max_m w_v(L,m,b)`), under
    which the identity is correct.

    CHECK: an explicit one-right-vertex instance where the literal reading
    gives 3/10 and the true lift value is 2/5.

Bounded computation; a regression check, not a proof.
"""
import itertools
import random
from fractions import Fraction


# ---------------------------------------------------------------- F_2^l utils

def invertible_matrices(l):
    """All invertible l x l matrices over F_2, as tuples of row masks."""
    out = []
    for rows in itertools.product(range(1, 1 << l), repeat=l):
        # rank over F_2 by gaussian elimination on the row masks
        basis = []
        for r in rows:
            v = r
            for b in basis:
                v = min(v, v ^ b)
            if v:
                basis.append(v)
                basis.sort(reverse=True)
        if len(basis) == l:
            out.append(rows)
    return out


def apply_mat(M, x):
    """Apply the matrix M (row masks) to the vector x (bitmask)."""
    y = 0
    for i, row in enumerate(M):
        if bin(row & x).count("1") & 1:
            y |= 1 << i
    return y


# --------------------------------------------- (A) the 2-to-2 -> 2-to-1 shape

def quotient_class(y, d):
    """Canonical representative of y + {0, d}."""
    return min(y, y ^ d)


def opt_2to2(n, l, cons):
    """Max weighted fraction of satisfied 2-to-2 constraints, brute force."""
    best = Fraction(0)
    for A in itertools.product(range(1 << l), repeat=n):
        s = Fraction(0)
        for (i, j, M, Mp, b, bp, w) in cons:
            if apply_mat(M, A[i]) ^ apply_mat(Mp, A[j]) in (b, bp):
                s += w
        best = max(best, s)
    return best


def val_bipartization(n, l, cons):
    """Edge-fraction value of B(U); the right side is optimised per constraint."""
    best = Fraction(0)
    for A in itertools.product(range(1 << l), repeat=n):
        s = Fraction(0)
        for (i, j, M, Mp, b, bp, w) in cons:
            d = b ^ bp
            c1 = quotient_class(apply_mat(M, A[i]) ^ b, d)
            c2 = quotient_class(apply_mat(Mp, A[j]), d)
            # best right label agrees with both if c1 == c2, else with one
            s += w if c1 == c2 else w / 2
        best = max(best, s)
    return best


def check_edge_maps_are_2to1(l, cons):
    """Every edge map of B(U) is exactly 2-to-1 onto 2^(l-1) classes."""
    for (i, j, M, Mp, b, bp, w) in cons:
        d = b ^ bp
        assert d != 0
        for shift, mat in ((b, M), (0, Mp)):
            fibres = {}
            for a in range(1 << l):
                fibres.setdefault(
                    quotient_class(apply_mat(mat, a) ^ shift, d), []).append(a)
            assert len(fibres) == 1 << (l - 1), fibres
            assert all(len(f) == 2 for f in fibres.values()), fibres


def run_A(trials=400, seed=20260918):
    rng = random.Random(seed)
    fails = 0
    for t in range(trials):
        l = rng.choice([1, 2, 3])
        mats = invertible_matrices(l)
        n = rng.randint(2, 4)
        m = rng.randint(2, 5)
        cons = []
        for _ in range(m):
            i = rng.randrange(n)
            j = rng.randrange(n)
            while j == i and n > 1:
                j = rng.randrange(n)
            b = rng.randrange(1 << l)
            bp = b
            while bp == b:
                bp = rng.randrange(1 << l)
            cons.append((i, j, rng.choice(mats), rng.choice(mats), b, bp,
                         Fraction(rng.randint(1, 5))))
        tot = sum(c[6] for c in cons)
        cons = [c[:6] + (c[6] / tot,) for c in cons]
        check_edge_maps_are_2to1(l, cons)
        opt = opt_2to2(n, l, cons)
        vb = val_bipartization(n, l, cons)
        if vb != (1 + opt) / 2:
            fails += 1
            print("  FAIL", l, n, opt, vb)
    print("(A) val(B(U)) = (1 + OPT(U))/2 on linear 2-to-2 instances: "
          "%d instances, %d failures" % (trials, fails))
    return fails


def run_A_worked_example():
    """Spell out the consequence on the gap parameters."""
    for eps in (Fraction(1, 10), Fraction(1, 100), Fraction(1, 1000)):
        yes = (1 + (1 - eps)) / 2
        no = (1 + eps) / 2
        assert no > Fraction(1, 2)
        print("    eps=%-8s  B maps [1-eps, eps] to [%s, %s]; soundness > 1/2"
              % (eps, yes, no))


# ------------------------------------------- (B) the branch-statistic formula

def run_B():
    """One right vertex, three left vertices; k = 2, left alphabet {0,1,2,3}.

    p_e: {0,1} -> 0, {2,3} -> 1 on every edge.
      u1, weight 3/10, label 0, p = 0, branch o(0) = 0
      u2, weight 3/10, label 1, p = 0, branch o(1) = 1
      u3, weight 4/10, label 2, p = 1, branch o(2) = 0
    """
    w = {"u1": Fraction(3, 10), "u2": Fraction(3, 10), "u3": Fraction(4, 10)}
    # (right label m, branch b) -> mass
    mass = {(0, 0): w["u1"], (0, 1): w["u2"], (1, 0): w["u3"]}
    mass_by_m = {}
    for (m, b), x in mass.items():
        mass_by_m[m] = mass_by_m.get(m, 0) + x

    val_G = max(mass_by_m.values())                       # best right label in G
    m_star = max(mass_by_m, key=lambda m: mass_by_m[m])
    val_lift = max(mass.values())                         # best (m, b) in U_o
    literal = max(mass.get((m_star, b), 0) for b in (0, 1))
    repaired = max(max(mass.get((m, b), 0) for m in (0, 1)) for b in (0, 1))

    print("(B) branch-statistic formula on the 3-edge instance:")
    print("    val(G)              = %s   (best right label m* = %d)"
          % (val_G, m_star))
    print("    val(U_o)            = %s   (true max over (m,b))" % val_lift)
    print("    literal claim-node  = %s   <-- strictly undercounts" % literal)
    print("    derivation reading  = %s   <-- agrees with val(U_o)" % repaired)
    ok = (val_lift == Fraction(2, 5) and literal == Fraction(3, 10)
          and repaired == val_lift and val_G / 2 <= val_lift <= val_G)
    print("    sandwich val(G)/2 <= val(U_o) <= val(G) still holds: %s"
          % (val_G / 2 <= val_lift <= val_G))
    print("(B) counterexample to the literal reading reproduced: %s" % ok)
    return 0 if ok else 1


if __name__ == "__main__":
    bad = run_A()
    run_A_worked_example()
    bad += run_B()
    raise SystemExit(1 if bad else 0)
