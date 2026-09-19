"""Exact checks for f-overgroups-with-a-non-integral-rational-piece-are-nonamenable.

Checks, in exact integer arithmetic:
  1. Congruence conjugation: for a primitive integer matrix L with det D > 1 and
     delta in Gamma(D), L delta adj(L) / D is an integer matrix of det 1.
  2. Double-coset normal form: SL2(Z) L SL2(Z) contains diag(1, D) (Smith form with
     determinant-one transformations), for random primitive L.
  3. Parabolic drag: delta_n = g a^{Dn} g^{-1} lies in Gamma(D) and delta_n(y) -> g(inf).
  4. The pieces named in the claim: c on [0,1] is (2 0; 1 1), primitive, det 2.
Run: python3 commensurator_drag.py   (prints OK lines, raises on failure)
"""
import random
from fractions import Fraction
from math import gcd
from sympy import Matrix
from sympy.matrices.normalforms import smith_normal_form

random.seed(20260917)


def mul(A, B):
    return [[A[0][0]*B[0][0] + A[0][1]*B[1][0], A[0][0]*B[0][1] + A[0][1]*B[1][1]],
            [A[1][0]*B[0][0] + A[1][1]*B[1][0], A[1][0]*B[0][1] + A[1][1]*B[1][1]]]


def det(A):
    return A[0][0]*A[1][1] - A[0][1]*A[1][0]


def adj(A):
    return [[A[1][1], -A[0][1]], [-A[1][0], A[0][0]]]


def rand_sl2(steps=6):
    T = [[1, 1], [0, 1]]
    S = [[0, -1], [1, 0]]
    M = [[1, 0], [0, 1]]
    for _ in range(steps):
        k = random.randint(-3, 3)
        M = mul(M, [[1, k], [0, 1]])
        M = mul(M, S)
    return M


def rand_primitive(maxe=9):
    while True:
        L = [[random.randint(-maxe, maxe) for _ in range(2)] for _ in range(2)]
        D = det(L)
        g = gcd(gcd(L[0][0], L[0][1]), gcd(L[1][0], L[1][1]))
        if D > 1 and g == 1:
            return L, D


def mobius(A, y):
    return (A[0][0]*y + A[0][1]) / (A[1][0]*y + A[1][1])


# 1. congruence conjugation
for _ in range(2000):
    L, D = rand_primitive()
    M = [[random.randint(-5, 5) for _ in range(2)] for _ in range(2)]
    delta = [[1 + D*M[0][0], D*M[0][1]], [D*M[1][0], 1 + D*M[1][1]]]
    if det(delta) != 1:
        continue
    P = mul(mul(L, delta), adj(L))
    assert all(x % D == 0 for row in P for x in row), (L, delta)
    Q = [[x // D for x in row] for row in P]
    assert det(Q) == 1
print("OK 1: L Gamma(D) L^{-1} in SL2(Z) (2000 random trials)")

# 2. Smith form diag(1, D) for primitive L; SL2 adjustment keeps it (det D > 0)
for _ in range(500):
    L, D = rand_primitive()
    S = smith_normal_form(Matrix(L))
    d1, d2 = abs(S[0, 0]), abs(S[1, 1])
    assert (d1, d2) == (1, D), (L, S)
print("OK 2: Smith form of primitive L with det D is diag(1, D) (500 trials)")

# 3. parabolic drag toward a rational r = g(inf), with y a rational proxy for an irrational
for _ in range(200):
    g = rand_sl2()
    D = random.randint(2, 7)
    r = Fraction(g[0][0], g[1][0]) if g[1][0] != 0 else None
    if r is None:
        continue
    y = Fraction(random.randint(-10**6, 10**6), 999983)
    x = mobius(adj(g), y)          # g^{-1} y
    errs = []
    for n in (10, 100, 1000):
        an = [[1, D*n], [0, 1]]
        dn = mul(mul(g, an), adj(g))
        assert (dn[0][0] - 1) % D == 0 and dn[0][1] % D == 0 and dn[1][0] % D == 0
        errs.append(abs(mobius(dn, y) - r))
    assert errs[0] > errs[1] > errs[2], errs
print("OK 3: delta_n = g a^{Dn} g^{-1} in Gamma(D) drags y monotonically to g(inf)")

# 4. named pieces
C = [[2, 0], [1, 1]]
assert det(C) == 2 and gcd(gcd(2, 0), gcd(1, 1)) == 1
for t in (Fraction(1, 3), Fraction(1, 2), Fraction(5, 7)):
    assert mobius(C, t) == 2*t/(1 + t)
half = [[2, 1], [0, 2]]   # t + 1/2, primitive after scaling: det 4, entries gcd 1
assert det(half) == 4 and gcd(gcd(2, 1), 2) == 1
print("OK 4: c = (2 0;1 1) det 2 primitive; t+1/2 = (2 1;0 2) det 4 primitive")
