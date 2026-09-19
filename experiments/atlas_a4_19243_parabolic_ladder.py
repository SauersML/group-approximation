#!/usr/bin/env python3
"""Exact subgroup ladder behind the A4 packet and collision 19243.

The packet-component and 19243 localization audits suggest a nested finite
geometry.  This script certifies it directly in GL(4,2).
"""

from atlas_a4_19243_component_localization import (
    H6_LABELS,
    H18_LABELS,
    Q_FIRST_INVOLUTION,
    Q_SECOND,
    I4,
    center,
    subgroup,
)


def fixes_last_row(matrix):
    return matrix[3] == (0, 0, 0, 1)


def fixes_last_column(matrix):
    return tuple(row[3] for row in matrix) == (0, 0, 0, 1)


def main():
    h6 = subgroup(H6_LABELS)
    h18 = subgroup(H18_LABELS)
    k = subgroup(Q_SECOND)
    z = center(h18)
    b = Q_FIRST_INVOLUTION

    # The two packet S3s visible before the central C3 is used generate the
    # standard block-diagonal GL(3,2).
    h = subgroup(tuple(h6 | k))
    assert len(h) == 168
    assert all(fixes_last_row(value) and fixes_last_column(value) for value in h)

    # Adding the repeated first-chart involution from q_19243 opens the
    # translation radical while preserving the last-row hyperplane.
    p = subgroup(tuple(h | {b}))
    assert len(p) == 1344
    assert all(fixes_last_row(value) for value in p)
    assert not all(fixes_last_column(value) for value in p)

    # The nontrivial center of H18 is exactly the ingredient which leaves that
    # maximal parabolic and completes the ambient A8=GL(4,2).
    nontrivial_z = [value for value in z if value != I4]
    assert len(nontrivial_z) == 2
    assert all(value not in p for value in nontrivial_z)
    full = subgroup(tuple(p | {nontrivial_z[0]}))
    assert len(full) == 20160

    print("<H6,K> is the standard block-diagonal GL(3,2), order 168")
    print("adjoining the q_19243 involution gives the hyperplane stabilizer, order 1344")
    print("adjoining either nontrivial central C3 element of H18 gives GL(4,2)=A8, order 20160")


if __name__ == "__main__":
    main()
