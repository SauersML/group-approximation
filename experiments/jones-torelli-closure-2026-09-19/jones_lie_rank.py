"""Exact Lie-algebra rank for Jones' rectangular (3,3) Temperley-Lieb module of TL_6(delta).

Claim checked (used in research/mod-s2-jones-torelli-closure-is-su5-proof.md):
  the complex span of the Lie brackets of depth >= 2 of e_1..e_5 is sl_5 for every delta outside the
  finite set of roots of an explicit nonzero polynomial P(delta), printed below.

Method (exact rational arithmetic, fractions.Fraction; sympy only to interpolate and factor P):
  1. e_i(delta) on the 5 noncrossing perfect matchings of 6 points, same conventions as
     experiments/jones-genus-two-near-scalar-2026-09-17/jones_tl6.py; TL relations checked exactly.
  2. Breadth-first brackets [e_i,e_j], [e_k,[e_i,e_j]], ...; keep a word when it raises the exact rank at
     delta0 = 3/2, until rank 24 = dim sl_5 (all brackets are traceless).
  3. Fix 24 matrix-entry columns with nonzero 24x24 minor at delta0. The minor is a polynomial in delta of
     degree <= sum of word depths (entries of a depth-k word have degree <= k). Evaluate it exactly at
     deg+1 integer points, interpolate, and check the interpolant at 3 further points.
  4. Wherever P(delta) != 0 the same 24 words are independent, so the depth >= 2 span is sl_5.
"""
import itertools
from fractions import Fraction as F
import sympy as sp

N, D = 6, 5


def matchings(pts):
    if not pts:
        yield []
        return
    a = pts[0]
    for k in range(1, len(pts), 2):
        for L in matchings(pts[1:k]):
            for R in matchings(pts[k + 1:]):
                yield [(a, pts[k])] + L + R


BASIS = [tuple(sorted(m)) for m in matchings(list(range(N)))]
IDX = {m: j for j, m in enumerate(BASIS)}
assert len(BASIS) == D


def partner(m):
    p = {}
    for a, b in m:
        p[a], p[b] = b, a
    return p


def E(i, dl):
    M = [[F(0)] * D for _ in range(D)]
    for j, m in enumerate(BASIS):
        p = partner(m)
        if p[i] == i + 1:
            M[j][j] += dl
        else:
            a, b = p[i], p[i + 1]
            new = [x for x in m if i not in x and i + 1 not in x] + [(i, i + 1), tuple(sorted((a, b)))]
            M[IDX[tuple(sorted(new))]][j] += 1
    return M


def mul(X, Y):
    return [[sum(X[r][k] * Y[k][c] for k in range(D)) for c in range(D)] for r in range(D)]


def sub(X, Y):
    return [[X[r][c] - Y[r][c] for c in range(D)] for r in range(D)]


def br(X, Y):
    return sub(mul(X, Y), mul(Y, X))


def iszero(X):
    return all(x == 0 for row in X for x in row)


def vec(X):
    return [X[r][c] for r in range(D) for c in range(D)]


def rank(rows):
    A = [list(r) for r in rows]
    rk, ncol = 0, len(A[0]) if A else 0
    for c in range(ncol):
        piv = next((r for r in range(rk, len(A)) if A[r][c] != 0), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        for r in range(len(A)):
            if r != rk and A[r][c] != 0:
                f = A[r][c] / A[rk][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[rk])]
        rk += 1
    return rk


def det(rows):
    A = [list(r) for r in rows]
    n, s = len(A), F(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return F(0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            s = -s
        s *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return s


def word_matrix(w, dl):
    """w = (k_1, ..., k_{n-2}, i, j) means [e_k1, [e_k2, ... [e_i, e_j]]]."""
    e = [E(i, dl) for i in range(N - 1)]
    X = br(e[w[-2]], e[w[-1]])
    for k in reversed(w[:-2]):
        X = br(e[k], X)
    return X


if __name__ == "__main__":
    # 1. TL relations: polynomial identities of degree <= 3 in delta, checked at 6 points => identically.
    for dl in [F(k, 7) for k in range(1, 7)]:
        e = [E(i, dl) for i in range(N - 1)]
        for i in range(5):
            assert iszero(sub(mul(e[i], e[i]), [[dl * x for x in row] for row in e[i]]))
            for j in range(5):
                if abs(i - j) == 1:
                    assert iszero(sub(mul(mul(e[i], e[j]), e[i]), e[i]))
                if abs(i - j) >= 2:
                    assert iszero(br(e[i], e[j]))
    print("TL relations: exact OK (identically in delta)")

    # 2. breadth-first words at delta0
    d0 = F(3, 2)
    e0 = [E(i, d0) for i in range(N - 1)]
    chosen, words = [], []
    frontier = []
    for i, j in itertools.combinations(range(5), 2):
        X = br(e0[i], e0[j])
        if iszero(X):
            continue
        frontier.append(((i, j), X))
        if rank([vec(Y) for Y in chosen + [X]]) > len(chosen):
            chosen.append(X); words.append((i, j))
    while len(chosen) < 24:
        nf = []
        for w, X in frontier:
            for k in range(5):
                Y = br(e0[k], X)
                if iszero(Y):
                    continue
                nf.append(((k,) + w, Y))
                if len(chosen) < 24 and rank([vec(Z) for Z in chosen + [Y]]) > len(chosen):
                    chosen.append(Y); words.append((k,) + w)
        frontier = nf
        assert frontier, "bracket closure stalled below 24"
    assert all(sum(X[r][r] for r in range(D)) == 0 for X in chosen)
    print("rank 24 at delta=3/2 reached; words:", words)
    print("max depth:", max(len(w) for w in words))

    # 3. fixed minor, interpolated exactly
    C0 = [vec(X) for X in chosen]
    cols = []
    for c in range(25):
        if rank([[row[k] for k in cols + [c]] for row in C0]) == len(cols) + 1:
            cols.append(c)
        if len(cols) == 24:
            break
    assert len(cols) == 24

    def minor(dl):
        return det([[vec(word_matrix(w, dl))[k] for k in cols] for w in words])

    deg = sum(len(w) for w in words)
    pts = list(range(deg + 1))
    x = sp.symbols('delta')
    P = sp.expand(sp.interpolate([(p, sp.Rational(minor(F(p)).numerator, minor(F(p)).denominator)) for p in pts], x))
    for t in [F(3, 2), F(-5, 3), F(deg + 7)]:
        v = minor(t)
        assert P.subs(x, sp.Rational(t.numerator, t.denominator)) == sp.Rational(v.numerator, v.denominator)
    assert P != 0
    print("degree bound", deg, "; P(delta) =", sp.factor(P))
    rr = sp.real_roots(sp.Poly(P, x))
    print("distinct real roots of P:", sorted(set(float(r) for r in rr)))
    print("roots in unitary window (sqrt2, 2]:", sorted(set(float(r) for r in rr if sp.sqrt(2) < r <= 2)))
