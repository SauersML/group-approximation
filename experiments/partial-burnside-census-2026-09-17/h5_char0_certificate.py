#!/usr/bin/env python3
"""Exact certificate: an infinite virtually abelian quotient of Pi_4(2,5).

Ring O = Z[z]/(1 + z + z^2 + z^3 + z^4) = Z[zeta_5], elements as integer
4-vectors in the basis 1, z, z^2, z^3.  Group elements are affine maps
(g, c) of O^5 with g = diag(z^v) Y^k monomial, (Y x)_i = x_{i+1}, and product
(g1, c1)(g2, c2) = (g1 g2, c1 + g1 c2).

    a = (X, c_a),  X = diag(1, z, z^2, z^3, z^4),  c_a = (0, 0, -z^2, 1, 0)
    b = (Y, 0)

The linear parts generate the Heisenberg group H5 (order 125, exponent 5).
The script checks EXACTLY, in O, that h^5 = 1 for every reduced word h in
a, b of length <= 4 (160 words), and prints every word of length 5 whose fifth
power is not 1; such a fifth power is a nonzero translation (its linear part
is 1 because H5 has exponent 5), which has infinite order in O^5.

Consequence: Q = <a, b> is a quotient of Pi_4(2,5) that is infinite, linear
over Z[zeta_5] and virtually abelian; reducing mod any prime ideal of O not
containing the translation entries gives finite quotients of order divisible
by q, for every prime q = 1 mod 5 (and powers), so of unbounded order.

Usage: python3 h5_char0_certificate.py
"""
from itertools import product

ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)


def radd(x, y):
    return tuple(a + b for a, b in zip(x, y))


def rneg(x):
    return tuple(-a for a in x)


def zpow_mul(e, x):
    """z^e * x in O."""
    c = tuple(x)
    for _ in range(e % 5):
        # z * (c0 + c1 z + c2 z^2 + c3 z^3) = c0 z + c1 z^2 + c2 z^3 + c3 z^4,
        # and z^4 = -1 - z - z^2 - z^3
        t = c[3]
        c = (-t, c[0] - t, c[1] - t, c[2] - t)
    return c


def lin_mul(g1, g2):
    v, k = g1
    u, l = g2
    return (tuple((v[i] + u[(i + k) % 5]) % 5 for i in range(5)), (k + l) % 5)


def lin_apply(g, x):
    v, k = g
    return tuple(zpow_mul(v[i], x[(i + k) % 5]) for i in range(5))


def aff_mul(A, B):
    g1, c1 = A
    g2, c2 = B
    gc = lin_apply(g1, c2)
    return (lin_mul(g1, g2), tuple(radd(c1[i], gc[i]) for i in range(5)))


ID = (((0, 0, 0, 0, 0), 0), (ZERO,) * 5)


def aff_pow(A, n):
    P = ID
    for _ in range(n):
        P = aff_mul(P, A)
    return P


def aff_inv(A):
    # A has order 5 in its linear part; A^-1 = A^4 * (A^5)^-1, and A^5 is a
    # translation t, so A^-1 = (translation by -t) * A^4.
    A4 = aff_pow(A, 4)
    A5 = aff_mul(A4, A)
    assert A5[0] == ID[0]
    negt = (ID[0], tuple(rneg(x) for x in A5[1]))
    return aff_mul(negt, A4)


def main():
    X = ((0, 1, 2, 3, 4), 0)
    Y = ((0, 0, 0, 0, 0), 1)
    a = (X, (ZERO, ZERO, rneg((0, 0, 1, 0)), ONE, ZERO))
    b = (Y, (ZERO,) * 5)
    gens = [a, aff_inv(a), b, aff_inv(b)]
    for s in range(4):
        assert aff_mul(gens[s], gens[s ^ 1]) == ID
    names = "aAbB"
    frontier = [((), ID)]
    count = 0
    for L in range(1, 6):
        nf, bad = [], []
        for w, e in frontier:
            for s in range(4):
                if w and w[-1] ^ 1 == s:
                    continue
                e2 = aff_mul(e, gens[s])
                w2 = w + (s,)
                p = aff_pow(e2, 5)
                assert p[0] == ID[0], "linear part not of exponent 5"
                if p != ID:
                    bad.append(("".join(names[t] for t in w2), p[1]))
                nf.append((w2, e2))
        frontier = nf
        if L <= 4:
            assert not bad, f"law fails at length {L}: {bad[:3]}"
            count += len(nf)
        else:
            print(f"all {count} reduced words of length <= 4 satisfy h^5 = 1 exactly over Z[zeta_5]")
            print(f"{len(bad)} of {len(nf)} words of length 5 have h^5 = nonzero translation; e.g.")
            for w, t in bad[:4]:
                print("  ", w, "h^5 = translation by", t)


if __name__ == "__main__":
    main()
