#!/usr/bin/env python3
"""Verify the periodic-Higman matrix certificate over Q(i)[L]/(P).

Standard library only. All arithmetic is exact; no floating point, random
search, or external computer algebra system is used. This checks the algebra
in research/artifacts/periodic-higman-cofinite-spectrum-2026-09-04.md,
not the imported primitive-divisor theorem or residual finiteness.
"""

from fractions import Fraction as F


# Gaussian rational coefficients, represented by (real, imaginary) pairs.
def g(a=0, b=0):
    return F(a), F(b)


def gadd(a, b):
    return a[0] + b[0], a[1] + b[1]


def gneg(a):
    return -a[0], -a[1]


def gmul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


GZERO, GONE = g(), g(1)
# Coefficients in ascending order; P is monic of degree five.
P = [g(0, 1), g(-3, -4), g(0, 2), g(2), g(-4, -3), GONE]


def residue(coefficients):
    """Unique degree < 5 remainder under monic polynomial division."""
    out = list(coefficients)
    while len(out) > 5:
        lead = out.pop()
        shift = len(out) - 5
        for j in range(5):
            out[shift + j] = gadd(out[shift + j], gneg(gmul(lead, P[j])))
    return tuple(out + [GZERO] * (5 - len(out)))


ZERO = residue([])
ONE = residue([GONE])
I = residue([g(0, 1)])
L = residue([GZERO, GONE])


def add(a, b):
    return tuple(gadd(x, y) for x, y in zip(a, b))


def neg(a):
    return tuple(gneg(x) for x in a)


def mul(a, b):
    out = [GZERO] * 9
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            out[j + k] = gadd(out[j + k], gmul(x, y))
    return residue(out)


def coefficients(pairs, denominator=1):
    return residue([(F(a, denominator), F(b, denominator)) for a, b in pairs])


X = coefficients([(-7, 8), (3, 3), (-3, -3), (-9, 11), (0, -3)], 8)
C = coefficients([(-5, 5), (0, 2), (-2, 4), (0, 6), (-1, -1)], 16)
W = coefficients([(0, -5), (-1, 5), (5, 3), (-5, -3), (1, 0)], 8)
K = coefficients([(4, -3), (-2, 0), (0, 2), (3, -4), (0, 1)])


def mmul(a, b):
    return tuple(
        tuple(add(mul(a[j][0], b[0][k]), mul(a[j][1], b[1][k])) for k in range(2))
        for j in range(2)
    )


def det(a):
    return add(mul(a[0][0], a[1][1]), neg(mul(a[0][1], a[1][0])))


def inverse_sl2(a):
    if det(a) != ONE:
        raise AssertionError("inverse_sl2 requires determinant one")
    return ((a[1][1], neg(a[0][1])), (neg(a[1][0]), a[0][0]))


def commutator(a, b):
    return mmul(mmul(mmul(inverse_sl2(a), inverse_sl2(b)), a), b)


def require_equal(name, actual, expected):
    if actual != expected:
        raise AssertionError(name)
    print("PASS:", name)


def main():
    require_equal("i^2 = -1", mul(I, I), neg(ONE))
    require_equal("P(L) = 0", residue(P), ZERO)
    require_equal("L K = 1", mul(L, K), ONE)
    a = ((X, ONE), (C, W))
    d = ((I, ZERO), (ZERO, ONE))
    di = ((neg(I), ZERO), (ZERO, ONE))
    t = ((L, ZERO), (ZERO, ONE))
    ti = ((K, ZERO), (ZERO, ONE))
    identity = ((ONE, ZERO), (ZERO, ONE))
    require_equal("T T^-1 = I", mmul(t, ti), identity)
    require_equal("D D^-1 = I", mmul(d, di), identity)
    h = [a]
    for _ in range(4):
        h.append(mmul(mmul(d, h[-1]), di))
    require_equal("A_4 = A_0", h[4], h[0])
    for j in range(4):
        require_equal(f"det(A_{j}) = 1", det(h[j]), ONE)
        require_equal(
            f"T A_{j} T^-1 = [A_{j}, A_{(j - 1) % 4}]",
            mmul(mmul(t, h[j]), ti),
            commutator(h[j], h[(j - 1) % 4]),
        )
    # At every prime over 2, i = 1; P reduces to (L+1)^5.
    mod2 = tuple(int(a + b) % 2 for a, b in P)
    from math import comb

    require_equal("P mod (2, i-1) = (L+1)^5", mod2, tuple(comb(5, j) % 2 for j in range(6)))
    print("Exact matrix certificate verified. No claim of residual finiteness is checked.")


if __name__ == "__main__":
    main()
