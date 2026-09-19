#!/usr/bin/env python3
"""Exact checks for p22-head-survival-forces-regular-weak-containment.

J = F_2<S,T | TS=1> with monomial basis S^i T^j, stored as pairs (i, j).
Q = 1 + ST (char 2).  P = P_{2,2}(J) = M_2(J) x| (EL_2(J) x EL_2(J)).

Part A  matrix units e_ij = S^i Q T^j, and the socle formula
        Q T^i a S^j Q = lambda_ij(a) Q,
        lambda_ij(a) = a_ij + sum_{k>=1} a_{i-k, j-k}          (Lemma 2)
        and the extraction Q = Q T^i a S^j Q at a support point of minimal i.
Part B  the Levi difference identities used in Lemma 1:
        x_12(b) Y - Y = E_12 b Y,   Y x_12(b)^{-1} - Y = Y E_12 b,
        (E_12 b)(E_21 c) = E_11 bc,  etc.
Part C  topological freeness (Lemma 4): for random Levi elements l = (A,B)
        with l != 1, the F_2-rank of D_l(Y) = A Y B^{-1} - Y on the window
        M_2(J_{<=n}) grows without bound in n.
Part D  the tensor-power spectral identity (Lemma 5) for genuine
        representations of a finite elementary abelian 2-group:
        E_chi(pi (x) pi') = sum_{psi psi' = chi} E_psi(pi) (x) E_psi'(pi').
Part E  the Archbold-Spielberg compression step (Lemma 6) in a finite model:
        for f supported on V and g with gV disjoint from V, h f u_g h = 0.

Exit status 0 iff every check passes.
"""
import itertools
import random
import sys

import numpy as np

random.seed(20260917)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL", msg)


# ---------------- the ring J ----------------

def mono_mul(a, b):
    i, j = a
    k, l = b
    if j <= k:
        return (i + k - j, l)
    return (i, j - k + l)


def add(x, y):
    return frozenset(set(x) ^ set(y))


def mul(x, y):
    out = set()
    for a in x:
        for b in y:
            out ^= {mono_mul(a, b)}
    return frozenset(out)


ZERO = frozenset()
ONE = frozenset({(0, 0)})
S = frozenset({(1, 0)})
T = frozenset({(0, 1)})
Q = frozenset({(0, 0), (1, 1)})


def Spow(i):
    return frozenset({(i, 0)})


def Tpow(j):
    return frozenset({(0, j)})


def e(i, j):
    return mul(mul(Spow(i), Q), Tpow(j))


def rand_elem(deg, density=0.3):
    return frozenset((i, j) for i in range(deg + 1) for j in range(deg + 1 - i)
                     if random.random() < density)


# ---------------- Part A ----------------

def part_a():
    n = 5
    for i, j, k, l in itertools.product(range(n), repeat=4):
        lhs = mul(e(i, j), e(k, l))
        rhs = e(i, l) if j == k else ZERO
        check(lhs == rhs, "matrix unit e%d%d e%d%d" % (i, j, k, l))
    check(mul(Q, S) == ZERO and mul(T, Q) == ZERO and mul(Q, Q) == Q,
          "QS = 0, TQ = 0, Q^2 = Q")
    trials = 0
    for _ in range(300):
        a = rand_elem(6)
        if not a:
            continue
        trials += 1
        for i in range(8):
            for j in range(8):
                val = mul(mul(mul(mul(Q, Tpow(i)), a), Spow(j)), Q)
                lam = ((i, j) in a)
                for k in range(1, min(i, j) + 1):
                    lam ^= ((i - k, j - k) in a)
                check(val == (Q if lam else ZERO), "socle formula at (%d,%d)" % (i, j))
        i0 = min(p[0] for p in a)
        j0 = min(p[1] for p in a if p[0] == i0)
        ext = mul(mul(mul(mul(Q, Tpow(i0)), a), Spow(j0)), Q)
        check(ext == Q, "extraction Q = Q T^i a S^j Q")
    print("Part A: matrix units (5^4 cases), socle formula and extraction on %d random a: ok"
          % trials)


# ---------------- 2x2 matrices over J ----------------

def m_mul(A, B):
    return tuple(tuple(add(mul(A[r][0], B[0][c]), mul(A[r][1], B[1][c]))
                       for c in range(2)) for r in range(2))


def m_add(A, B):
    return tuple(tuple(add(A[r][c], B[r][c]) for c in range(2)) for r in range(2))


I2 = ((ONE, ZERO), (ZERO, ONE))


def Eab(a, b, x):
    M = [[ZERO, ZERO], [ZERO, ZERO]]
    M[a][b] = x
    return tuple(tuple(r) for r in M)


def x12(b):
    return ((ONE, b), (ZERO, ONE))


def x21(b):
    return ((ONE, ZERO), (b, ONE))


def rand_mat(deg):
    return tuple(tuple(rand_elem(deg) for _ in range(2)) for _ in range(2))


def part_b():
    for _ in range(100):
        Y = rand_mat(4)
        b = rand_elem(3)
        c = rand_elem(3)
        # in char 2, x_12(b)^{-1} = x_12(b)
        check(m_mul(x12(b), x12(b)) == I2, "x12(b) involution")
        check(m_add(m_mul(x12(b), Y), Y) == m_mul(Eab(0, 1, b), Y), "left difference 12")
        check(m_add(m_mul(x21(b), Y), Y) == m_mul(Eab(1, 0, b), Y), "left difference 21")
        check(m_add(m_mul(Y, x12(b)), Y) == m_mul(Y, Eab(0, 1, b)), "right difference 12")
        check(m_add(m_mul(Y, x21(b)), Y) == m_mul(Y, Eab(1, 0, b)), "right difference 21")
        check(m_mul(Eab(0, 1, b), Eab(1, 0, c)) == Eab(0, 0, mul(b, c)), "E12 b E21 c = E11 bc")
        check(m_mul(Eab(1, 0, b), Eab(0, 1, c)) == Eab(1, 1, mul(b, c)), "E21 b E12 c = E22 bc")
    print("Part B: Levi difference identities and matrix-unit products on 100 random samples: ok")


# ---------------- Part C ----------------

LEFT_GENS = [x12(S), x12(T), x21(ONE), x12(ONE), x21(S), x21(T)]


def rand_levi_word(length):
    A = I2
    for _ in range(length):
        A = m_mul(A, random.choice(LEFT_GENS))
    return A


def inv_word_product(word):
    return word  # every generator is an involution; see rand_levi_pair


def rand_levi_pair(length):
    wa = [random.choice(LEFT_GENS) for _ in range(length)]
    wb = [random.choice(LEFT_GENS) for _ in range(random.randint(0, length))]
    A = I2
    for g in wa:
        A = m_mul(A, g)
    B = I2
    Binv = I2
    for g in wb:
        B = m_mul(B, g)
    for g in reversed(wb):
        Binv = m_mul(Binv, g)
    check(m_mul(B, Binv) == I2, "B B^{-1} = 1")
    return A, B, Binv


def window_basis(n):
    monos = [(i, j) for i in range(n + 1) for j in range(n + 1 - i)]
    basis = []
    for a in range(2):
        for b in range(2):
            for m in monos:
                basis.append(Eab(a, b, frozenset({m})))
    return basis


def encode(M, index):
    v = 0
    for r in range(2):
        for c in range(2):
            for m in M[r][c]:
                key = (r, c, m)
                if key not in index:
                    index[key] = len(index)
                v |= 1 << index[key]
    return v


def gf2_rank(vectors):
    pivots = {}
    rank = 0
    for v in vectors:
        while v:
            h = v.bit_length() - 1
            if h in pivots:
                v ^= pivots[h]
            else:
                pivots[h] = v
                rank += 1
                break
    return rank


def part_c():
    tested = 0
    for _ in range(12):
        A, B, Binv = rand_levi_pair(random.randint(1, 5))
        if A == I2 and B == I2:
            continue
        tested += 1
        ranks = []
        for n in (2, 4, 6, 8):
            index = {}
            imgs = [encode(m_add(m_mul(m_mul(A, Y), Binv), Y), index) for Y in window_basis(n)]
            ranks.append(gf2_rank(imgs))
        check(ranks[-1] > ranks[0] and all(ranks[k] < ranks[k + 1] for k in range(3)),
              "rank of D_l grows: %s" % ranks)
    print("Part C: %d random Levi elements l != 1, rank of D_l strictly increasing in the window: ok"
          % tested)


# ---------------- Part D ----------------

def part_d():
    r = 3
    F = list(itertools.product(range(2), repeat=r))
    chars = F  # psi(Y) = (-1)^{<psi, Y>}

    def ev(psi, Y):
        return -1 if sum(p * y for p, y in zip(psi, Y)) % 2 else 1

    def rep(mult):
        # genuine representation: diagonal, character psi with multiplicity mult[psi]
        diag = []
        for psi in chars:
            diag += [psi] * mult[psi]
        return {Y: np.diag([ev(psi, Y) for psi in diag]).astype(float) for Y in F}

    def proj(pi, chi):
        d = next(iter(pi.values())).shape[0]
        out = np.zeros((d, d))
        for Y in F:
            out += ev(chi, Y) * pi[Y]
        return out / len(F)

    for _ in range(20):
        m1 = {psi: random.randint(0, 2) for psi in chars}
        m2 = {psi: random.randint(0, 2) for psi in chars}
        if sum(m1.values()) == 0 or sum(m2.values()) == 0:
            continue
        p1, p2 = rep(m1), rep(m2)
        pt = {Y: np.kron(p1[Y], p2[Y]) for Y in F}
        for chi in chars:
            lhs = proj(pt, chi)
            rhs = sum(np.kron(proj(p1, psi), proj(p2, tuple((a + b) % 2 for a, b in zip(psi, chi))))
                      for psi in chars)
            check(np.allclose(lhs, rhs), "tensor spectral identity")
        # spectrum of the tensor product is the product set of the spectra
        sp1 = {psi for psi in chars if m1[psi]}
        sp2 = {psi for psi in chars if m2[psi]}
        prod = {tuple((a + b) % 2 for a, b in zip(x, y)) for x in sp1 for y in sp2}
        spt = {chi for chi in chars if np.linalg.norm(proj(pt, chi)) > 0.5}
        check(spt == prod, "spectrum of tensor product is product set")
    print("Part D: tensor-power spectral identity and product-set spectrum on random reps of (Z/2)^3: ok")


# ---------------- Part E ----------------

def part_e():
    # X = Z/12 with the rotation action; g = rotation by 5 has no fixed points.
    n = 12
    shift = 5
    U = np.zeros((n, n))
    for x in range(n):
        U[(x + shift) % n, x] = 1.0
    for _ in range(50):
        f = np.diag(np.random.rand(n))
        V = [0, 1]
        h = np.diag([1.0 if x in V else 0.0 for x in range(n)])
        check(np.allclose(h @ f @ U @ h, 0), "h f u_g h = 0 when gV and V are disjoint")
    print("Part E: compression h f u_g h = 0 on disjoint supports: ok")


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
    part_e()
    if FAIL:
        print("%d FAILURES" % len(FAIL))
        sys.exit(1)
    print("all checks passed")
    sys.exit(0)
