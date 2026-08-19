#!/usr/bin/env python3
"""Exact finite calibration for the 19243 centrality gap.

The four aligned second-chart syllables of collision 19243 are
r,s,r^-1,sr with <r,s> ~= S3, and the repeated first-chart syllable is b.
For every relative unitary commuting with r and s, equivariance reduces the
collision word to the fixed first-chart involution b.  The canonical
centrality test uses x=p1_12.  This script checks the finite GL_4(F_2)
identities

    F(b)=r b s b r^-1 b (s r) b = b,
    [x,b] != 1.

The latter makes the regular-character normalized-HS defect exactly sqrt(2).
"""

from __future__ import annotations

import json


R_HEX = "01000000000001000001010000000001"
S_HEX = "01000000000101000000010000000001"
B_HEX = "01000000000100000000010100000001"
X_HEX = "01000000000101000000010000000001"  # p1_12


def matrix(hex_value):
    raw = bytes.fromhex(hex_value)
    return tuple(tuple(raw[4 * i + j] & 1 for j in range(4)) for i in range(4))


def identity():
    return tuple(tuple(int(i == j) for j in range(4)) for i in range(4))


def mul(a, b):
    return tuple(tuple(
        sum(a[i][k] * b[k][j] for k in range(4)) & 1
        for j in range(4)) for i in range(4))


def inv(a):
    aug = [list(a[i]) + list(identity()[i]) for i in range(4)]
    for col in range(4):
        pivot = next(row for row in range(col, 4) if aug[row][col])
        aug[col], aug[pivot] = aug[pivot], aug[col]
        for row in range(4):
            if row != col and aug[row][col]:
                aug[row] = [u ^ v for u, v in zip(aug[row], aug[col])]
    return tuple(tuple(row[4:]) for row in aug)


def product(*values):
    out = identity()
    for value in values:
        out = mul(out, value)
    return out


def commutator(a, b):
    return product(a, b, inv(a), inv(b))


def order(a):
    power = identity()
    for exponent in range(1, 20):
        power = mul(power, a)
        if power == identity():
            return exponent
    raise ValueError("order too large")


def main():
    r, s, b, x = map(matrix, (R_HEX, S_HEX, B_HEX, X_HEX))
    assert order(r) == 3
    assert order(s) == order(b) == order(x) == 2
    assert product(s, r, s) == inv(r)
    f_b = product(r, b, s, b, inv(r), b, s, r, b)
    assert f_b == b
    centrality_value = commutator(x, b)
    assert centrality_value != identity()

    print(json.dumps({
        "S3_relations": {
            "order_r": order(r),
            "order_s": order(s),
            "srs_is_r_inverse": product(s, r, s) == inv(r),
        },
        "collision_equivariance_calibration": {
            "F_b_equals_b": f_b == b,
            "b_order": order(b),
        },
        "centrality_test": {
            "x": "p1_12",
            "commutator_nontrivial": centrality_value != identity(),
            "commutator_order": order(centrality_value),
            "regular_trace": 0,
            "normalized_hs_distance_to_identity_squared": 2,
        },
        "word_lipschitz_constants": {
            "collision_in_relative_unitary": 8,
            "centrality_in_relative_unitary": 16,
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
