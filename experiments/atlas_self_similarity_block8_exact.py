"""Verify the exact 8D self-similarity phase over Q(zeta_8).

Run with SageMath.  Every assertion is exact; there is no floating-point
arithmetic or optimization.
"""

import json

from sage.all import CyclotomicField, diagonal_matrix, identity_matrix, matrix


def permutation_involution(field, dimension, pairs):
    value = matrix(field, dimension, dimension)
    for left, right in pairs:
        value[left, right] = 1
        value[right, left] = 1
    return value


def main():
    field = CyclotomicField(8)
    zeta = field.gen()
    identity = identity_matrix(field, 8)

    # Canonical restriction 2*tau plus all four D8 linear characters.
    b = matrix(field, 8, 8)
    c = matrix(field, 8, 8)
    for offset in (0, 2):
        b[offset, offset + 1] = 1
        b[offset + 1, offset] = 1
        c[offset, offset] = 1
        c[offset + 1, offset + 1] = -1
    for offset, (b_sign, c_sign) in enumerate(
            ((-1, -1), (-1, 1), (1, -1), (1, 1)), start=4):
        b[offset, offset] = b_sign
        c[offset, offset] = c_sign

    reversal = permutation_involution(
        field, 8, ((0, 7), (1, 6), (2, 5), (3, 4)))
    bridge = permutation_involution(
        field, 8, ((0, 6), (2, 4), (5, 3), (7, 1)))
    square_root = diagonal_matrix(field, [
        zeta if c[index, index] == 1 else zeta ** -1
        for index in range(8)
    ])

    a = b * bridge * b
    e = bridge * reversal * square_root
    relation = a * b * e * b * a * b * e * c * b
    y = b * a * b * e

    assert b ** 2 == identity
    assert c ** 2 == identity
    assert (b * c) ** 4 == identity
    assert bridge ** 2 == identity
    assert reversal ** 2 == identity
    assert bridge * c == -c * bridge
    assert bridge * reversal == reversal * bridge
    assert reversal * c == c * reversal
    assert a ** 2 == identity
    assert e ** 2 == identity
    assert a.conjugate().transpose() == a
    assert e.conjugate().transpose() == e
    assert a * e == e * a
    assert a.trace() == 0
    assert e.trace() == 0
    assert (a * e).trace() == 0
    for a_sign in (-1, 1):
        for e_sign in (-1, 1):
            projector = ((identity + a_sign * a)
                         * (identity + e_sign * e) / 4)
            assert projector.rank() == 2
    assert y ** 2 == zeta ** 2 * c
    assert relation == zeta ** 2 * identity

    print(json.dumps({
        "field": "Q(zeta_8)",
        "dimension": 8,
        "D8_faithful_multiplicity": 2,
        "D8_linear_character_multiplicities": [1, 1, 1, 1],
        "V4_character_multiplicities": [2, 2, 2, 2],
        "relation": "i I_8",
        "verified_exactly": True,
    }, indent=2))


if __name__ == "__main__":
    main()
