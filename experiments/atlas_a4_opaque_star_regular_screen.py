#!/usr/bin/env python3
"""Screen the opaque-star transports on exact regular A8 packet alignments.

For an inner or outer chart alignment ``alpha`` and a transvection ``t``, the
relative covariance opcode in the left regular representation is the group
unitary

    lambda(alpha(t) t^-1).

Its spectrum depends only on the order of ``alpha(t) t^-1``: it is the
uniform measure on those roots of unity.  Hence two such regular opcodes can
be unitarily conjugate only when their group orders agree.

The script reuses the established exhaustive list of thirty inner and thirty
outer exact alignments for the A4 packet and records the four opcode orders
for the minimal transvection cycle t01,t12,t23,t30 (hub t23).
"""

import collections

from atlas_a4_classical_two_holonomy_profile import transformed
from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


def transvection(row, column):
    value = I4.copy()
    value[row, column] ^= 1
    return value


TRANSVECTIONS = (
    ("t01", transvection(0, 1)),
    ("t12", transvection(1, 2)),
    ("t23", transvection(2, 3)),
    ("t30", transvection(3, 0)),
)


def order(matrix):
    value = I4.copy()
    for exponent in range(1, 16):
        value = gf2_mul(value, matrix)
        if matrix_key(value) == matrix_key(I4):
            return exponent
    raise AssertionError("element order exceeds the GL(4,2) bound")


def word_value(word, alignment, inverse, use_outer):
    value = I4.copy()
    for factor, matrix in word:
        image = transformed(matrix, alignment, inverse, use_outer) if factor == 2 else matrix
        value = gf2_mul(value, image)
    return value


def audit(packet, use_outer):
    identity = matrix_key(I4)
    profiles = collections.Counter()
    witnesses = []
    for alignment in enumerate_gl4():
        inverse = gf2_inv(alignment)
        if not all(
            matrix_key(word_value(word, alignment, inverse, use_outer)) == identity
            for _index, word in packet
        ):
            continue

        profile = tuple(
            order(gf2_mul(transformed(t, alignment, inverse, use_outer), t))
            for _name, t in TRANSVECTIONS
        )
        profiles[profile] += 1
        if any(profile[index] != profile[2] for index in (0, 1, 3)):
            witnesses.append((matrix_key(alignment).hex(), profile))

    assert sum(profiles.values()) == 30
    return profiles, witnesses


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())

    expected = {
        "inner": (22, ("00000100010000000001000000000001", (4, 4, 2, 2))),
        "outer": (20, ("00000100010000000001000000000001", (2, 2, 4, 4))),
    }
    for branch, use_outer in (("inner", False), ("outer", True)):
        profiles, witnesses = audit(packet, use_outer)
        assert (len(witnesses), witnesses[0]) == expected[branch]
        print(branch, "profiles", dict(sorted(profiles.items())))
        print(branch, "nonconjugate_star_witnesses", len(witnesses))
        if witnesses:
            print(branch, "first_witness", witnesses[0])


if __name__ == "__main__":
    main()
