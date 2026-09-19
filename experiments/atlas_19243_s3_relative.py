#!/usr/bin/env python3
"""Exact finite calibration for atlas collision word 19243.

After the stored classical alignment, the four second-chart syllables of
collision 19243 are r, s, r^2, s r with <r,s> ~= S3, while all four
first-chart syllables are the same involution b.  Conjugating the whole word
by the relative chart unitary reduces the relation to

    r c s c r^2 c (s r) c = 1,      c = U* b U.

This script verifies that c=(13)(24), together with r=(123), s=(12), gives
an exact S4 solution.  It also records the multiplicity calculation which
lifts this S3-relative solution to the regular A8 chart size 20160:

    Reg(A8)|S3 = 3360 Reg(S3),
    840 Reg(S4)|S3 = 3360 Reg(S3).

No floating-point arithmetic is used.
"""

from __future__ import annotations

import json


ALIGNMENT_HEX = "00000100000100000100000000000001"
SECOND_HEX = (
    "01010000010000000000010000000001",
    "01000000010100000000010000000001",
    "00010000010100000000010000000001",
    "01010000000100000000010000000001",
)
FIRST_INVOLUTION_HEX = "01000000000100000000010100000001"


def gf2_matrix(hex_value: str):
    raw = bytes.fromhex(hex_value)
    if len(raw) != 16:
        raise ValueError("expected a 4 by 4 F2 matrix")
    return tuple(tuple(raw[4 * i + j] & 1 for j in range(4)) for i in range(4))


def gf2_mul(a, b):
    return tuple(tuple(
        sum(a[i][k] * b[k][j] for k in range(4)) & 1
        for j in range(4)) for i in range(4))


def gf2_identity():
    return tuple(tuple(int(i == j) for j in range(4)) for i in range(4))


def gf2_inverse(a):
    aug = [list(a[i]) + list(gf2_identity()[i]) for i in range(4)]
    for col in range(4):
        pivot = next((row for row in range(col, 4) if aug[row][col]), None)
        if pivot is None:
            raise ValueError("singular matrix")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        for row in range(4):
            if row != col and aug[row][col]:
                aug[row] = [x ^ y for x, y in zip(aug[row], aug[col])]
    return tuple(tuple(row[4:]) for row in aug)


def gf2_order(a, limit=20):
    power = gf2_identity()
    for exponent in range(1, limit + 1):
        power = gf2_mul(power, a)
        if power == gf2_identity():
            return exponent
    raise ValueError("order exceeds limit")


def perm_mul(left, right):
    """Function composition: (left * right)(x)=left(right(x))."""
    return tuple(left[right[x]] for x in range(len(left)))


def perm_inv(value):
    out = [0] * len(value)
    for source, target in enumerate(value):
        out[target] = source
    return tuple(out)


def perm_order(value):
    identity = tuple(range(len(value)))
    power = identity
    for exponent in range(1, 100):
        power = perm_mul(power, value)
        if power == identity:
            return exponent
    raise ValueError("permutation order too large")


def cycle(size, *cycles):
    value = list(range(size))
    for cyc in cycles:
        for old, new in zip(cyc, cyc[1:] + cyc[:1]):
            value[old] = new
    return tuple(value)


def generated_subgroup(generators):
    identity = tuple(range(len(generators[0])))
    seen = {identity}
    frontier = [identity]
    while frontier:
        old = frontier.pop()
        for generator in generators:
            new = perm_mul(old, generator)
            if new not in seen:
                seen.add(new)
                frontier.append(new)
    return seen


def main():
    alignment = gf2_matrix(ALIGNMENT_HEX)
    alignment_inverse = gf2_inverse(alignment)
    aligned = tuple(
        gf2_mul(gf2_mul(alignment, gf2_matrix(value)), alignment_inverse)
        for value in SECOND_HEX
    )
    r, s, r2, sr = aligned
    b = gf2_matrix(FIRST_INVOLUTION_HEX)

    assert gf2_order(r) == 3
    assert gf2_order(s) == 2
    assert r2 == gf2_mul(r, r) == gf2_inverse(r)
    assert sr == gf2_mul(s, r)
    assert gf2_mul(gf2_mul(s, r), s) == gf2_inverse(r)
    assert gf2_order(b) == 2

    # S4 calibration, on points 0,1,2,3:
    # r=(0 1 2), s=(0 1), c=(0 2)(1 3).
    r4 = cycle(4, (0, 1, 2))
    s4 = cycle(4, (0, 1))
    c4 = cycle(4, (0, 2), (1, 3))
    identity4 = tuple(range(4))
    relation = identity4
    for factor in (r4, c4, s4, c4, perm_inv(r4), c4,
                   perm_mul(s4, r4), c4):
        relation = perm_mul(relation, factor)
    assert relation == identity4
    assert perm_order(c4) == 2
    subgroup = generated_subgroup((r4, s4, c4))
    assert len(generated_subgroup((r4, s4))) == 6
    assert len(subgroup) == 24

    a8_order = 20160
    s3_order = 6
    s4_order = 24
    a8_s3_regular_multiplicity = a8_order // s3_order
    s4_amplification = a8_order // s4_order
    amplified_s4_s3_multiplicity = s4_amplification * (s4_order // s3_order)
    assert a8_s3_regular_multiplicity == amplified_s4_s3_multiplicity == 3360

    print(json.dumps({
        "aligned_second_syllable_orders": [gf2_order(value) for value in aligned],
        "aligned_normal_form": ["r", "s", "r^2", "s r"],
        "first_syllable_order": gf2_order(b),
        "relative_relation": "r c s c r^-1 c (s r) c = 1",
        "s4_solution": {
            "r": "(1 2 3)",
            "s": "(1 2)",
            "c": "(1 3)(2 4)",
            "relation_holds": True,
            "generated_group_order": len(subgroup),
            "s3_subgroup_order": len(generated_subgroup((r4, s4))),
        },
        "regular_margin_lift": {
            "A8_order": a8_order,
            "Reg_A8_restricted_to_S3_multiplicity": a8_s3_regular_multiplicity,
            "S4_regular_copies": s4_amplification,
            "amplified_Reg_S4_restricted_to_S3_multiplicity":
                amplified_s4_s3_multiplicity,
            "ambient_dimension": a8_order,
            "balanced_involution_trace": 0,
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
