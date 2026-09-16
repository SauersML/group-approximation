#!/usr/bin/env python3
"""Peripheral torus test for the Long-Reid family rho_k of the figure-eight knot group.

Source of the matrices: D. D. Long and A. W. Reid, "Small subgroups of SL(3,Z)",
preprint dated August 18, 2010 (Proposition 2.1), transcribed by hand from the
PDF layout; the transcription is validated below by checking the relations.

Gamma = < x, y, z | z x z^-1 = x y, z y z^-1 = y x y >, fibre F = <x, y>.
The monodromy fixes c = [x,y] exactly, so rho_k(z) commutes with C_k = rho_k(c).

For each integer k in a window this script:
  1. checks det = 1 and both relations exactly (sympy integer matrices);
  2. checks the characteristic polynomial of C_k against p_k from Lemma 2.4;
  3. computes disc(p_k), irreducibility over Q, and the signature;
  4. checks [Z_k, C_k] = 1 and writes Z_k = a + b C_k + c C_k^2 over Q;
  5. decides whether Z_k and C_k are multiplicatively dependent:
     - complex cubic (disc < 0): the unit rank is 1, so they are dependent;
       an explicit relation Z^m = +-C^n is searched and verified exactly;
     - totally real (disc > 0): the 2x2 log-embedding determinant is computed
       with 60 digits; a value far from 0 certifies independence.
Single-threaded; small output.
"""
import sympy as sp
from sympy import Matrix, Poly, symbols
import mpmath

mpmath.mp.dps = 60
Q = symbols("Q")


def mats(k):
    X = Matrix([[1, -2, 3], [0, k, -1 - 2 * k], [0, 1, -2]])
    Y = Matrix([[-2 - k, -1, 1], [-2 - k, -2, 3], [-1, -1, 2]])
    Z = Matrix([[0, 0, 1], [1, 0, -k], [0, 1, -1 - k]])
    return X, Y, Z


def p_k(k):
    return sp.expand(1 + (-17 - 2 * k - 2 * k ** 2) * Q
                     + (6 - 8 * k - 7 * k ** 2 + 2 * k ** 3 + k ** 4) * Q ** 2 - Q ** 3)


def find_relation(Z, C, bound=60):
    I = sp.eye(3)
    powsC = {0: I}
    Ci = C.inv()
    P, M = I, I
    for n in range(1, bound + 1):
        P = P * C
        M = M * Ci
        powsC[n] = P
        powsC[-n] = M
    Zm = I
    for m in range(1, bound + 1):
        Zm = Zm * Z
        for n, Cn in powsC.items():
            if Zm == Cn:
                return (m, n, +1)
            if Zm == -Cn:
                return (m, n, -1)
    return None


def analyse(k):
    X, Y, Z = mats(k)
    assert X.det() == 1 and Y.det() == 1 and Z.det() == 1
    assert Z * X * Z.inv() == X * Y, k
    assert Z * Y * Z.inv() == Y * X * Y, k
    C = X * Y * X.inv() * Y.inv()
    cp = C.charpoly(Q).as_expr()
    assert sp.expand(-cp - p_k(k)) == 0, (k, cp)
    assert Z * C == C * Z
    poly = Poly(-p_k(k), Q)
    disc = sp.discriminant(poly.as_expr(), Q)
    irreducible = poly.is_irreducible
    # Z = a I + b C + c C^2 over Q
    a, b, c = symbols("a b c")
    sol = sp.solve(list(a * sp.eye(3) + b * C + c * C * C - Z), [a, b, c], dict=True)
    assert len(sol) == 1
    abc = (sol[0][a], sol[0][b], sol[0][c])
    rec = {"k": k, "disc": int(disc), "irreducible": irreducible, "Z_in_Q[C]": abc}
    if disc < 0:
        rel = find_relation(Z, C)
        rec["relation Z^m = sign*C^n"] = rel
    else:
        coeffs = [int(cf) for cf in poly.all_coeffs()]
        roots = mpmath.polyroots(coeffs, maxsteps=400, extraprec=400)
        assert all(abs(mpmath.im(r)) < mpmath.mpf(10) ** (-40) for r in roots)
        roots = [mpmath.re(r) for r in roots]
        fa = [mpmath.mpf(int(sp.Rational(v).p)) / int(sp.Rational(v).q) for v in abc]
        us = [fa[0] + fa[1] * r + fa[2] * r * r for r in roots]
        lt = [mpmath.log(abs(r)) for r in roots]
        lu = [mpmath.log(abs(u)) for u in us]
        detv = lt[0] * lu[1] - lt[1] * lu[0]
        rec["log-embedding det"] = mpmath.nstr(detv, 12)
        rec["independent"] = abs(detv) > mpmath.mpf(10) ** (-30)
    return rec


def main():
    Ksym = symbols("k")
    D = sp.discriminant(-p_k(Ksym), Q)
    print("disc(p_k) =", sp.factor(D))
    for k in range(-12, 13):
        print(analyse(k))


if __name__ == "__main__":
    main()
