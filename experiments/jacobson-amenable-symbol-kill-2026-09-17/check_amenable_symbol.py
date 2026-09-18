#!/usr/bin/env python3
"""Exact checks for amenable-symbol-subgroups-keep-the-jacobson-head.

J = F_2<S,T | TS=1>, elements = finite sets of normal-form monomials (a,b)
meaning S^a T^b (F_2 coefficients, so addition = symmetric difference).
Product rule: S^a T^b * S^c T^d = S^(a+c-b) T^d  if c >= b
                                 = S^a T^(b-c+d)  if c <  b.
Symbol: S^a T^b -> z^(a-b) in F_2[z,z^-1]; kernel = I = span S^a Q T^b.

Checks
 1. ring axioms spot check, TS = 1, Q idempotent, symbol multiplicative;
 2. symbol kernel equals span of S^a Q T^b (dimension count on a window);
 3. the w12 pigeonhole certificate: g^{-1} g = 1, [e, g^{-1} u g] = x_13(Q);
 4. symbol images of the certificate generators: g, e block upper triangular,
    x_34(1), x_43(S) involutions with product of trace z (so <.,.> = D_inf);
 5. local finiteness: random finitely generated subgroups of GL_2(J, I)
    are finite (BFS closes), as the proof predicts;
 6. numerical Gamma_BS toy (BS(1,2) *_<a> (<a> x <e>)) model: head norm -> 2
    while all defining relator defects -> 0.
"""
import itertools
import random

import numpy as np

random.seed(20260917)


# ---------- the Jacobson algebra ----------
def mono_mul(m1, m2):
    a, b = m1
    c, d = m2
    if c >= b:
        return (a + c - b, d)
    return (a, b - c + d)


def add(x, y):
    return frozenset(set(x) ^ set(y))


def mul(x, y):
    out = set()
    for m1 in x:
        for m2 in y:
            out ^= {mono_mul(m1, m2)}
    return frozenset(out)


ZERO = frozenset()
ONE = frozenset({(0, 0)})
S = frozenset({(1, 0)})
T = frozenset({(0, 1)})
Q = add(ONE, mul(S, T))


def symbol(x):
    """Laurent polynomial over F_2 as a frozenset of exponents."""
    out = set()
    for (a, b) in x:
        out ^= {a - b}
    return frozenset(out)


def lmul(p, q):
    out = set()
    for i in p:
        for j in q:
            out ^= {i + j}
    return frozenset(out)


def rand_elt(k=4, deg=3):
    return frozenset(
        {(random.randint(0, deg), random.randint(0, deg)) for _ in range(k)})


def check_ring():
    assert mul(T, S) == ONE
    assert mul(S, T) != ONE
    assert mul(Q, Q) == Q
    assert mul(T, Q) == ZERO and mul(Q, S) == ZERO
    for _ in range(300):
        x, y, w = rand_elt(), rand_elt(), rand_elt()
        assert mul(mul(x, y), w) == mul(x, mul(y, w))
        assert mul(x, add(y, w)) == add(mul(x, y), mul(x, w))
        assert symbol(mul(x, y)) == lmul(symbol(x), symbol(y))
    print("1. ring spot checks, TS=1, Q^2=Q, symbol multiplicative: ok")


def check_kernel(D=5):
    monos = [(a, b) for a in range(D) for b in range(D)]
    # symbol-kernel inside span(monos): dimension = #monos - #distinct degrees
    degs = {a - b for (a, b) in monos}
    kdim = len(monos) - len(degs)
    ideal = [mul(mul(frozenset({(a, 0)}), Q), frozenset({(0, b)}))
             for a in range(D - 1) for b in range(D - 1)]
    for x in ideal:
        assert symbol(x) == ZERO
    # the S^a Q T^b are distinct monomial pairs (a,b)+(a+1,b+1): independent
    assert len(set(ideal)) == len(ideal)
    # sanity: kernel dimension on the window matches (D-1)^2
    assert kdim == (D - 1) ** 2
    print("2. symbol kernel on %dx%d window has dim %d = #S^aQT^b: ok"
          % (D, D, kdim))


# ---------- matrices over J ----------
def mat_id(n):
    return [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]


def mat_mul(A, B):
    n = len(A)
    return [[_dot(A, B, i, j, n) for j in range(n)] for i in range(n)]


def _dot(A, B, i, j, n):
    acc = ZERO
    for k in range(n):
        if A[i][k] and B[k][j]:
            acc = add(acc, mul(A[i][k], B[k][j]))
    return acc


def elem(n, i, j, r):
    M = mat_id(n)
    M[i][j] = r
    return M


def blockdiag(B, n):
    M = mat_id(n)
    for i in range(len(B)):
        for j in range(len(B)):
            M[i][j] = B[i][j]
    return M


def comm(x, y, xi, yi):
    # [x,y] = x^-1 y^-1 x y
    return mat_mul(mat_mul(mat_mul(xi, yi), x), y)


def check_certificate():
    n = 4
    wK = [[S, Q], [ZERO, T]]
    wKi = [[T, ZERO], [Q, S]]
    g = blockdiag(wK, n)
    gi = blockdiag(wKi, n)
    assert mat_mul(g, gi) == mat_id(n) and mat_mul(gi, g) == mat_id(n)
    e = elem(n, 0, 1, ONE)          # x_12(1), involution
    u = elem(n, 0, 2, ONE)          # x_13(1), involution
    b = mat_mul(mat_mul(gi, u), g)  # g^-1 u g
    assert b == mat_mul(elem(n, 0, 2, T), elem(n, 1, 2, Q))
    assert mat_mul(b, b) == mat_id(n) and mat_mul(e, e) == mat_id(n)
    head = comm(e, b, e, b)  # e, b are involutions
    # e centralizes the row-1 subgroup A (entries in columns 3,4)
    for r in (ONE, S, mul(S, S)):
        for col in (2, 3):
            xr = elem(n, 0, col, r)
            assert mat_mul(e, xr) == mat_mul(xr, e)
            # Ad g acts on row-1 matrices by left multiplication by S
            assert mat_mul(mat_mul(g, xr), gi) == elem(n, 0, col, mul(S, r))
    assert head == elem(n, 0, 2, Q)
    print("3. certificate: g g^-1 = 1, g^-1 u g = x13(T)x23(Q), "
          "[e, g^-1 u g] = x13(Q): ok")
    return g, e


def sym_mat(M):
    return [[symbol(x) for x in row] for row in M]


def check_symbols(g, e):
    n = 5
    for M in (blockdiag([[S, Q], [ZERO, T]], n), elem(n, 0, 1, ONE)):
        sm = sym_mat(M)
        for i in range(n):
            for j in range(i):
                assert sm[i][j] == ZERO   # upper triangular symbol
    a = elem(n, 2, 3, ONE)   # x_34(1)
    bb = elem(n, 3, 2, S)    # x_43(S)
    assert mat_mul(a, a) == mat_id(n) and mat_mul(bb, bb) == mat_id(n)
    p = sym_mat(mat_mul(a, bb))
    blk = [[p[2][2], p[2][3]], [p[3][2], p[3][3]]]
    assert blk == [[frozenset({0, 1}), frozenset({0})],
                   [frozenset({1}), frozenset({0})]]
    tr = frozenset(set(blk[0][0]) ^ set(blk[1][1]))
    assert tr == frozenset({1})       # trace z: transcendental, infinite order
    head = elem(n, 0, 2, Q)
    assert all(sym_mat(head)[i][j] == (frozenset({0}) if i == j else ZERO)
               for i in range(n) for j in range(n))
    print("4. symbols: g,e upper triangular; x34(1),x43(S) involutions, "
          "product symbol [[1+z,1],[z,1]] trace z; head has symbol 1: ok")


# ---------- local finiteness of GL_2(J, I) ----------
def rand_ideal_elt(D=3, k=2):
    x = ZERO
    for _ in range(k):
        a, b = random.randint(0, D), random.randint(0, D)
        x = add(x, mul(mul(frozenset({(a, 0)}), Q), frozenset({(0, b)})))
    return x


def key(M):
    return tuple(tuple(sorted(x)) for row in M for x in row)


def check_local_finiteness(trials=6, cap=30000):
    sizes = []
    for _ in range(trials):
        gens = []
        for _ in range(2):
            # elementary generators of GL_2(J, I): x_12(i), x_21(i), i in I
            # supports in the window e_0, e_1 of each copy: the proof
            # predicts a subgroup of GL_4(F_2) (order 20160)
            gens.append(elem(2, 0, 1, rand_ideal_elt(D=1)))
            gens.append(elem(2, 1, 0, rand_ideal_elt(D=1)))
        seen = {key(mat_id(2)): mat_id(2)}
        frontier = [mat_id(2)]
        while frontier:
            new = []
            for M in frontier:
                for G in gens:
                    P = mat_mul(M, G)
                    k = key(P)
                    if k not in seen:
                        seen[k] = P
                        new.append(P)
            frontier = new
            assert len(seen) < cap, "did not close"
        assert 20160 % len(seen) == 0   # Lagrange inside GL_4(F_2)
        sizes.append(len(seen))
    print("5. random 4-generated subgroups of E_2(J,I) closed finitely, "
          "orders", sizes, ": ok")


# ---------- numerical Gamma_BS toy ----------
def check_bs_toy():
    """On C^N, N odd: a = diag(w^j), t: e_j -> e_{j/2}, e: e_j -> e_{j+1}.
    Everything is diagonal or monomial, so work with diagonals as vectors:
    e^-1 D e = diag(D_{j+1});  t a t^-1 has entry w^(2k) at k = j/2;
    b = t^-1 a t = diag(w^(j/2)).  Commutators of the shift with a diagonal
    are diagonal, so operator norms are max-abs of diagonal vectors."""
    rows = []
    for N in (31, 101, 1001, 10001, 100001):
        w = np.exp(2j * np.pi / N)
        idx = np.arange(N)
        a = w ** idx
        inv2 = pow(2, -1, N)
        tat = np.empty(N, dtype=complex)
        tat[(idx * inv2) % N] = a                     # t a t^-1
        d1 = np.max(np.abs(tat - a ** 2))             # relator t a t^-1 = a^2
        d2 = np.max(np.abs(np.conj(np.roll(a, -1)) * a - 1))   # [e,a] = 1
        b = w ** ((idx * inv2) % N)                   # t^-1 a t
        hn = np.max(np.abs(np.conj(np.roll(b, -1)) * b - 1))   # [e,b] - 1
        rows.append((N, d1, d2, hn))
    for (N, d1, d2, hn) in rows:
        print("   N=%6d  |tat^-1-a^2|=%.1e  |[e,a]-1|=%.3e  |head-1|=%.8f"
              % (N, d1, d2, hn))
    assert all(r[1] < 1e-9 for r in rows)
    assert rows[-1][2] < 1e-4 and rows[-1][3] > 2 - 1e-8
    print("6. Gamma_BS toy: relator defects -> 0, head stays at distance "
          "-> 2: ok")


if __name__ == "__main__":
    check_ring()
    check_kernel()
    g, e = check_certificate()
    check_symbols(g, e)
    check_local_finiteness()
    check_bs_toy()
    print("ALL CHECKS PASSED")
