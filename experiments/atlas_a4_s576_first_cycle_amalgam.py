#!/usr/bin/env python3
"""Certify the first post-S288 core edge by a 576-point regular amalgam."""

import json

from atlas_a4_regular_amalgam_finite_search import (
    B,
    BETA,
    I4,
    POINTS,
    POINT_INDEX,
    R,
    Z,
    compose,
    generated_order,
    inverse,
    semilinear_collision,
)


DELTA = (1, 0, 2, 3)
DELTA_INV = inverse(DELTA)


def conjugate_delta(value):
    return compose(DELTA, compose(value, DELTA_INV))


D = tuple(POINT_INDEX[(conjugate_delta(first), conjugate_delta(second))]
          for first, second in POINTS)
C = semilinear_collision(I4)
U = compose(C, D)


def cycle(*cycles):
    result = list(I4)
    for values in cycles:
        for old, new in zip(values, values[1:] + values[:1]):
            result[old] = new
    return tuple(result)


A = cycle((0, 1))
S = cycle((1, 2))
B4 = cycle((2, 3))
U4 = compose(A, B4)
Y4 = compose(B4, S)


def pair_mul(left, right):
    return compose(left[0], right[0]), left[1] ^ right[1]


def pair_subgroup_order(generators):
    identity = (I4, 0)
    seen = {identity}
    todo = [identity]
    while todo:
        old = todo.pop()
        for generator in generators:
            new = pair_mul(old, generator)
            if new not in seen:
                seen.add(new)
                todo.append(new)
    return len(seen)


def main():
    assert BETA == cycle((0, 1), (2, 3))
    assert compose(C, D) == compose(D, C)
    assert compose(U, U) == tuple(range(144))
    assert compose(U, R) == compose(inverse(R), U)
    assert compose(U, Z) == compose(Z, U)
    assert compose(U, C) == compose(C, U)
    assert compose(U, B) == compose(B, U)

    h_prime_order = generated_order((R, Z, B, C, D))
    first_packet_order = generated_order((R, Z, C, U))
    carrier_order = generated_order((R, Z, B))
    overlap_order = generated_order((B, C, U))
    assert (h_prime_order, first_packet_order, carrier_order, overlap_order) == (
        576, 36, 144, 8)

    c4 = (I4, 1)
    b4 = (B4, 0)
    u4 = (U4, 0)
    y4 = (Y4, 0)
    l_order = pair_subgroup_order(((A, 0), (S, 0), (B4, 0), c4))
    j_order = pair_subgroup_order((b4, y4, c4))
    a4_edge_order = pair_subgroup_order((u4, y4))
    e_order = pair_subgroup_order((b4, u4, c4))
    assert (l_order, j_order, a4_edge_order, e_order) == (48, 12, 12, 8)
    assert pair_subgroup_order((pair_mul(u4, y4),)) == 3

    assert 576 // 8 == 12 * (48 // 8) == 72
    print(json.dumps({
        "left_group_order": h_prime_order,
        "first_packet_S3xS3_order": first_packet_order,
        "forward_carrier_order": carrier_order,
        "right_group_order": l_order,
        "collision_J_order": j_order,
        "new_A4_edge_order": a4_edge_order,
        "common_C2_cubed_order": overlap_order,
        "ambient_permutation_degree": 576,
        "Reg_left_restricted_overlap_copies": 576 // 8,
        "12_Reg_right_restricted_overlap_copies": 12 * (48 // 8),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
