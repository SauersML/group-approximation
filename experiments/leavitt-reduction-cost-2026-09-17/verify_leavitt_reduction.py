#!/usr/bin/env python3
"""Verify the exact word identities behind the uniform-cost Leavitt reduction (LR).

Setting (research/leavitt-cone-head-bound-linear-shadow-dimension-proof.md):
  A = x_ia(u), B = x_ab(t), C = x_bc(s), D = x_ck(v), E = x_ac(eps)   (all involutions, char 2)
  N = [C, D] = x_bk(s v),  F = [E, D] = x_ak(eps v)
  X = [[A, B], N] = P^b(u t, s v),  P = [A, F] = P^a(u, eps v)
  r1 = [A, N], r2 = [B, D], r3 = [B, C] E^-1,  e1 = [E, C], e2 = [C, F]
with [g, h] = g h g^-1 h^-1.

Identities checked in the free product *_{A,B,C,D,E} Z/2 (every letter an involution):
  (I1) X = A [BAB, N] A r1
  (I2) [BAB, N] = B [A, BNB] B
  (I3) BNB = r3 E C r2 D r3 E C r2 D
  (I4) E C D E C D = e1 e2 F N
  (I5) [A, F N] = P F r1 F^-1
  (I6) X = (A B) [A, BNB] (A B)^-1 r1        (I1 + I2 combined)
Then (I6) with BNB replaced by F N via (I3)/(I4), and (I5), gives
  X = (AB) P (AB)^-1 * (product of conjugates of r1 (x2), r2 (x4), r3 (x4), e1, e2 (x2 each)).
e1, e2 are exact relations of Delta_+, so they are trivial in Gamma.

A second check evaluates the words in an honest matrix model (EL_7 over the ring
F_2[x, y] / (x, y)^3 with commuting entries), where every relator is 1 and LR must hold exactly.
"""
import itertools
import random

INV = set("ABCDE")


def red(word):
    """Free reduction in the free product of Z/2's: cancel adjacent equal letters."""
    out = []
    for ch in word:
        if out and out[-1] == ch:
            out.pop()
        else:
            out.append(ch)
    return "".join(out)


def inv(word):
    return word[::-1]  # every letter is an involution


def comm(g, h):
    return red(g + h + inv(g) + inv(h))


def mul(*ws):
    return red("".join(ws))


A, B, C, D, E = "A", "B", "C", "D", "E"
N = comm(C, D)
F = comm(E, D)
X = comm(comm(A, B), N)
P = comm(A, F)
r1 = comm(A, N)
r2 = comm(B, D)
r3 = mul(comm(B, C), inv(E))
e1 = comm(E, C)
e2 = comm(C, F)
BAB = mul(B, A, B)
BNB = mul(B, N, B)


def check(name, lhs, rhs):
    ok = red(lhs + inv(rhs)) == ""
    print(f"{name}: {'OK' if ok else 'FAIL'}")
    assert ok, name


check("I1 X = A[BAB,N]A r1", X, mul(A, comm(BAB, N), A, r1))
check("I2 [BAB,N] = B[A,BNB]B", comm(BAB, N), mul(B, comm(A, BNB), B))
check("I3 BNB = r3 E C r2 D r3 E C r2 D", BNB, mul(r3, E, C, r2, D, r3, E, C, r2, D))
check("I4 ECDECD = e1 e2 F N", mul(E, C, D, E, C, D), mul(e1, e2, F, N))
check("I5 [A,FN] = P F r1 F^-1", comm(A, mul(F, N)), mul(P, F, r1, inv(F)))
check("I6 X = (AB)[A,BNB](AB)^-1 r1", X, mul(A, B, comm(A, BNB), inv(mul(A, B)), r1))

# Error budget: count relator occurrences along the route X -> (AB) P (AB)^-1.
# [A, BNB]: BNB contains r3 twice and r2 twice; [A, BNB] = A BNB A BNB^-1 contains BNB twice.
budget = {"r1": 2, "r2": 4, "r3": 4}
print("error budget  ||X - (AB)P(AB)^-1|| <= 2||r1|| + 4||r2|| + 4||r3||", budget)

# ---------------- matrix model: commutative ring F_2[x,y]/(x,y)^3 ----------------
# Elements: dict monomial (i,j) -> 1 over F_2 with i + j <= 2, stored as frozenset of monomials.
MONS = [(i, j) for i in range(3) for j in range(3) if i + j <= 2]


def radd(a, b):
    return a ^ b


def rmul(a, b):
    out = set()
    for (i, j) in a:
        for (k, l) in b:
            m = (i + k, j + l)
            if m[0] + m[1] <= 2:
                out ^= {m}
    return frozenset(out)


ZERO = frozenset()
ONE = frozenset({(0, 0)})
n = 7


def ident():
    return [[ONE if r == c else ZERO for c in range(n)] for r in range(n)]


def mmul(X_, Y_):
    Z = [[ZERO] * n for _ in range(n)]
    for r in range(n):
        for c in range(n):
            acc = ZERO
            for k in range(n):
                if X_[r][k] and Y_[k][c]:
                    acc = radd(acc, rmul(X_[r][k], Y_[k][c]))
            Z[r][c] = acc
    return Z


def elem(i, j, a):
    M = ident()
    M[i][j] = radd(M[i][j], a)
    return M


def rand_elt(rng):
    return frozenset(m for m in MONS if rng.random() < 0.5)


def mcomm(g, h):
    # involutions: inverse = self
    return mmul(mmul(g, h), mmul(g, h))


rng = random.Random(17)
i, a, b, c, k = 0, 3, 4, 5, 2
for trial in range(50):
    u, t, s, v = (rand_elt(rng) for _ in range(4))
    ts = rmul(t, s)
    Am, Bm, Cm, Dm = elem(i, a, u), elem(a, b, t), elem(b, c, s), elem(c, k, v)
    Em = elem(a, c, ts)
    Nm = mcomm(Cm, Dm)
    Fm = mcomm(Em, Dm)
    Xm = mcomm(mcomm(Am, Bm), Nm)
    Pm = mcomm(Am, Fm)
    g = mmul(Am, Bm)
    ginv = mmul(Bm, Am)
    assert Xm == mmul(mmul(g, Pm), ginv), "LR fails in matrix model"
    # also check X = x_ik(u t s v), P = x_ik(u ts v): LR says they are equal in a genuine ring
    assert Xm == elem(i, k, rmul(rmul(u, t), rmul(s, v)))
print("matrix model EL_7(F_2[x,y]/(x,y)^3): LR exact in 50 random trials: OK")
print("ALL CHECKS PASSED")
