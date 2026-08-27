#!/usr/bin/env python3
"""Exact audit of the symmetric-sign packet normalization loss.

For S_m this checks the sign-idempotent convolution identity and prints the
three squared scales relevant to an Amitsur packet compression.
"""

from fractions import Fraction
from itertools import permutations
from math import factorial


def compose(p, q):
    """Return p after q, with permutations stored as image tuples."""
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p):
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def sign(p):
    inversions = sum(
        p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p))
    )
    return -1 if inversions % 2 else 1


def audit(m):
    group = list(permutations(range(m)))
    order = factorial(m)
    assert len(group) == order

    # For e_- = |G|^{-1} sum sign(sigma) lambda(sigma), the coefficient
    # of lambda(tau) in e_-^2 is sign(tau)/|G|.
    probes = group if order <= 120 else group[:: max(1, order // 31)]
    for tau in probes:
        total = 0
        for sigma in group:
            rho = compose(inverse(sigma), tau)
            total += sign(sigma) * sign(rho)
        assert total == order * sign(tau)

    sign_trace = Fraction(1, order)
    coefficient_norm_sq = Fraction(1, order)
    ambient_block_norm_sq = Fraction(1, order * order)
    return order, sign_trace, coefficient_norm_sq, ambient_block_norm_sq


def main():
    print("m\t|S_m|\ttau(e_sign)\tcoefficient_norm_sq\tambient_block_norm_sq")
    for m in range(2, 8):
        order, trace, coefficient, ambient = audit(m)
        print(f"{m}\t{order}\t{trace}\t{coefficient}\t{ambient}")


if __name__ == "__main__":
    main()
