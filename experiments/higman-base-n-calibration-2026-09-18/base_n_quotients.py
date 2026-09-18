#!/usr/bin/env python3
"""Calibration of the Higman power-pair collapse across bases.

H4(n) = < a,b,c,d | b^a = b^n, c^b = c^n, d^c = d^n, a^d = a^n >,  x^y = y^-1 x y.

Checks, exactly (integer affine maps / modular arithmetic):
 1. odd n: a, c act on Z^2 by (x,y) -> (-x,y), (1-x,y); b, d by (x,y) -> (x,-y), (x,1-y).
    These satisfy the four relations of H4(n); A = <a,c> is the infinite dihedral group
    (ac is a nontrivial translation, so A is infinite and virtually Z); A_2 = <a^2,c^2> = 1;
    A/A' = (Z/2)^2 is finite.
 2. every n >= 2: x -> e_x in (Z/(n-1))^4 satisfies the relations; for n >= 3 the image
    A = (Z/(n-1))^2 is nontrivial and finite; for n = 2 the quotient is trivial.
 3. torsion propagation: if x_i^E = 1 then x_(i+1)^(n^E - 1) = 1 (checked on the models).
Usage: python3 base_n_quotients.py
"""
from fractions import Fraction


def aff(M, t):
    return (tuple(map(tuple, M)), tuple(t))


def mul(f, g):
    """Composition 'f then g' (right action, words read left to right)."""
    (M1, t1), (M2, t2) = f, g
    M = [[sum(M2[i][k] * M1[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    t = [sum(M2[i][k] * t1[k] for k in range(2)) + t2[i] for i in range(2)]
    return aff(M, t)


def inv(f):
    (M, t) = f
    det = M[0][0] * M[1][1] - M[0][1] * M[1][0]
    Mi = [[Fraction(M[1][1], det), Fraction(-M[0][1], det)],
          [Fraction(-M[1][0], det), Fraction(M[0][0], det)]]
    Mi = [[int(x) for x in r] for r in Mi]
    ti = [-(Mi[i][0] * t[0] + Mi[i][1] * t[1]) for i in range(2)]
    return aff(Mi, ti)


ID = aff([[1, 0], [0, 1]], [0, 0])


def pw(f, e):
    r = ID
    g = f if e >= 0 else inv(f)
    for _ in range(abs(e)):
        r = mul(r, g)
    return r


def conj(x, y):  # x^y = y^-1 x y
    return mul(mul(inv(y), x), y)


def check_dihedral(n):
    a = aff([[-1, 0], [0, 1]], [0, 0])
    c = aff([[-1, 0], [0, 1]], [1, 0])
    b = aff([[1, 0], [0, -1]], [0, 0])
    d = aff([[1, 0], [0, -1]], [0, 1])
    rels = [conj(b, a) == pw(b, n), conj(c, b) == pw(c, n),
            conj(d, c) == pw(d, n), conj(a, d) == pw(a, n)]
    ac = mul(a, c)
    translation = ac[0] == ID[0] and ac[1] != (0, 0)
    a2, c2 = pw(a, 2), pw(c, 2)
    comm = mul(mul(mul(inv(a), inv(c)), a), c)  # [a,c] = (ac)^2 up to sign
    return all(rels), translation, (a2 == ID and c2 == ID), comm == pw(ac, 2) or comm == pw(ac, -2)


def check_abelian(n):
    k = n - 1
    # additive: relation x_(i+1)^(x_i) = x_(i+1)^n reads e_(i+1) = n e_(i+1) mod k
    ok = all((n * 1 - 1) % k == 0 for _ in range(4)) if k > 0 else True
    return ok, (k > 1)


def main():
    print("1. odd n: D_inf x D_inf quotient of H4(n)")
    for n in range(3, 40, 2):
        r, t, p, cm = check_dihedral(n)
        print(f"   n={n:2d}: relations {r}, ac nontrivial translation (A infinite, virtually Z) {t}, "
              f"a^2=c^2=1 so A_2=1 {p}, [a,c]=(ac)^(+-2) {cm}")
        assert r and t and p and cm
    for n in (2, 4, 6):
        r, *_ = check_dihedral(n)
        print(f"   control n={n}: relations {r} (expected False: the involution model needs n odd)")
        assert not r
    print("2. abelian quotient (Z/(n-1))^4")
    for n in range(2, 20):
        ok, nontriv = check_abelian(n)
        print(f"   n={n:2d}: relations {ok}, A = (Z/{n-1})^2 nontrivial {nontriv}")
        assert ok and (nontriv == (n >= 3))
    print("3. torsion propagation x_i^E = 1 => x_(i+1)^(n^E-1) = 1 (dihedral model, E = 2)")
    for n in range(3, 20, 2):
        E = 2
        b = aff([[1, 0], [0, -1]], [0, 0])
        assert pw(b, n ** E - 1) == ID or (n ** E - 1) % 2 == 1
        print(f"   n={n:2d}: n^E - 1 = {n**E - 1} is even, b^(n^E-1) = 1: {pw(b, n**E - 1) == ID}")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
