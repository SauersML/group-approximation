#!/usr/bin/env python3
"""Checks for sp4-hilbert-modular-subgroup-deligne-rigidity-proof.

For K = Q(sqrt m) (m = 2, 5 handled; any squarefree m > 1 works the same way):

  E1 (exact, fractions).  Lambda = O_K e1 + d^{-1} e2, omega(x, y) = tr_{K/Q} det[x y].
      Gram matrix of omega on a Z-basis of Lambda is integral, alternating, det 1.
      Generators of B = Stab(Lambda) in SL_2(K) (upper unipotents with entries in d,
      lower unipotents with entries in d^{-1}, the fundamental unit torus, and an
      element w = [[0, b], [-1/b, 0]] with b a generator of d) act by integer
      matrices preserving the Gram matrix.
  E2 (numerical).  Winding number in pi_1(Sp_4(R)) = Z of the loops
      theta -> (R_theta, 1), (1, R_theta), (R_theta, R_theta) in SL_2(R)^2,
      embedded through the two real places.  Expected 1, 1, 2, so the induced map
      pi_1(SL_2(R)^2) = Z^2 -> Z is (m, n) -> m + n.

Pure python + numpy.  Prints ALL PASS at the end.
"""
from fractions import Fraction as F
import math
import numpy as np


class K:
    """Elements a + b sqrt(m) with rational a, b."""
    m = 2

    def __init__(self, a, b=0):
        self.a, self.b = F(a), F(b)

    def __add__(s, o):
        o = o if isinstance(o, K) else K(o)
        return K(s.a + o.a, s.b + o.b)

    def __neg__(s):
        return K(-s.a, -s.b)

    def __sub__(s, o):
        return s + (-(o if isinstance(o, K) else K(o)))

    def __mul__(s, o):
        o = o if isinstance(o, K) else K(o)
        return K(s.a * o.a + K.m * s.b * o.b, s.a * o.b + s.b * o.a)

    def inv(s):
        n = s.a * s.a - K.m * s.b * s.b
        return K(s.a / n, -s.b / n)

    def tr(s):
        return 2 * s.a

    def emb(s, sign):
        return float(s.a) + sign * float(s.b) * math.sqrt(K.m)


def setup(m):
    K.m = m
    r = K(0, 1)
    if m % 4 == 1:
        w = K(F(1, 2), F(1, 2))          # O_K = Z[(1+sqrt m)/2], different = (sqrt m)
        obasis = [K(1), w]
        dgen = r                          # d = (sqrt m)
        unit = {5: K(F(1, 2), F(1, 2))}[m]
    else:
        obasis = [K(1), r]                # O_K = Z[sqrt m], different = (2 sqrt m)
        dgen = K(0, 2)
        unit = {2: K(1, 1), 3: K(2, 1), 6: K(5, 2), 7: K(8, 3)}[m]
    dinv = dgen.inv()
    lam = [(x, K(0)) for x in obasis] + [(K(0), x * dinv) for x in obasis]
    return obasis, dgen, dinv, unit, lam


def omega(x, y):
    return (x[0] * y[1] - x[1] * y[0]).tr()


def coords(v, lam):
    """Solve v = sum c_i lam_i over Q (4x4 rational system)."""
    rows = []
    for comp in (0, 1):
        for part in ("a", "b"):
            rows.append([getattr(l[comp], part) for l in lam])
    rhs = [getattr(v[0], "a"), getattr(v[0], "b"), getattr(v[1], "a"), getattr(v[1], "b")]
    n = 4
    M = [rows[i][:] + [rhs[i]] for i in range(n)]
    for c in range(n):
        p = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[p] = M[p], M[c]
        M[c] = [x / M[c][c] for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                M[i] = [a - M[i][c] * b for a, b in zip(M[i], M[c])]
    return [M[i][n] for i in range(n)]


def act(g, v):
    (a, b), (c, d) = g
    return (a * v[0] + b * v[1], c * v[0] + d * v[1])


def det4(M):
    return round(np.linalg.det(np.array(M, dtype=float)))


def e1(m):
    obasis, dgen, dinv, unit, lam = setup(m)
    G = [[omega(x, y) for y in lam] for x in lam]
    assert all(x.denominator == 1 for row in G for x in row), G
    assert all(G[i][j] == -G[j][i] for i in range(4) for j in range(4))
    assert det4(G) == 1, det4(G)
    gens = []
    for x in obasis:
        gens.append(((K(1), x * dgen), (K(0), K(1))))
        gens.append(((K(1), K(0)), (x * dinv, K(1))))
    gens.append(((unit, K(0)), (K(0), unit.inv())))
    gens.append(((K(0), dgen), (-dgen.inv(), K(0))))
    for g in gens:
        (a, b), (c, d) = g
        assert (a * d - b * c).a == 1 and (a * d - b * c).b == 0
        M = [coords(act(g, l), lam) for l in lam]   # row i = image of basis vector i
        assert all(x.denominator == 1 for row in M for x in row), M
        for i in range(4):
            for j in range(4):
                assert omega(act(g, lam[i]), act(g, lam[j])) == G[i][j]
    print(f"E1 m={m}: Gram integral alternating det 1; {len(gens)} generators integral and symplectic")


def winding(loop, N=2000):
    """pi_1(Sp_4(R)) winding of a loop given in coordinates (q1,q2,p1,p2), omega standard."""
    phases = []
    for k in range(N + 1):
        M = loop(2 * math.pi * k / N)
        U, _, Vt = np.linalg.svd(M)
        O = U @ Vt                           # orthogonal symplectic part = [[A,-B],[B,A]]
        A, B = O[:2, :2], O[2:, :2]
        phases.append(np.angle(np.linalg.det(A + 1j * B)))
    un = np.unwrap(phases)
    return round((un[-1] - un[0]) / (2 * math.pi))


def e2(m):
    K.m = m
    def rot(t):
        return np.array([[math.cos(t), -math.sin(t)], [math.sin(t), math.cos(t)]])

    def embed(g1, g2):
        # planes: place 1 coordinates (q1,p1), place 2 (q2,p2); omega = det + det
        M = np.zeros((4, 4))
        M[np.ix_([0, 2], [0, 2])] = g1
        M[np.ix_([1, 3], [1, 3])] = g2
        J = np.block([[np.zeros((2, 2)), np.eye(2)], [-np.eye(2), np.zeros((2, 2))]])
        assert np.allclose(M.T @ J @ M, J)
        return M
    # also check that omega = tr det splits as det + det over the real places
    x = (K(F(3, 7), 2), K(-1, F(5, 3)))
    y = (K(2, F(-1, 4)), K(F(1, 2), 1))
    lhs = float(omega(x, y))
    rhs = sum(x[0].emb(s) * y[1].emb(s) - x[1].emb(s) * y[0].emb(s) for s in (1, -1))
    assert abs(lhs - rhs) < 1e-9
    I = np.eye(2)
    w = [winding(lambda t: embed(rot(t), I)), winding(lambda t: embed(I, rot(t))),
         winding(lambda t: embed(rot(t), rot(t)))]
    assert w == [1, 1, 2], w
    print(f"E2 m={m}: tr det = det(place 1) + det(place 2); windings (R,1),(1,R),(R,R) = {w}")


if __name__ == "__main__":
    for m in (2, 3, 5):
        e1(m)
    e2(2)
    print("ALL PASS")
