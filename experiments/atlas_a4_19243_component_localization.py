#!/usr/bin/env python3
"""Exact F2 localization of collision 19243 inside the A4 packet components.

The newest packet audit identifies the large component as S3 x C3.  This
script checks which factor collision 19243 actually sees and what is generated
when its repeated first-chart involution is adjoined.

Everything is exact in GL(4,2); there is no floating-point arithmetic.
"""

from collections import Counter


I4 = tuple(tuple(int(i == j) for j in range(4)) for i in range(4))


def matrix(hex_value):
    raw = bytes.fromhex(hex_value)
    if len(raw) != 16:
        raise ValueError("expected 4 by 4 F2 matrix")
    return tuple(tuple(raw[4 * i + j] & 1 for j in range(4)) for i in range(4))


def mul(a, b):
    return tuple(tuple(
        sum(a[i][k] * b[k][j] for k in range(4)) & 1
        for j in range(4)) for i in range(4))


def order(a):
    value = I4
    for exponent in range(1, 32):
        value = mul(value, a)
        if value == I4:
            return exponent
    raise AssertionError("order too large")


def subgroup(generators):
    seen = {I4}
    todo = [I4]
    while todo:
        old = todo.pop()
        for generator in generators:
            new = mul(old, generator)
            if new not in seen:
                seen.add(new)
                todo.append(new)
    return seen


def center(group):
    return {a for a in group if all(mul(a, b) == mul(b, a) for b in group)}


def commute(a, b):
    return mul(a, b) == mul(b, a)


# Exact component labels from atlas_a4_packet_component_audit.py.
H6_LABELS = tuple(map(matrix, (
    "01000000000101000000010000000001",
    "01000000000100000001010000000001",
    "01000000000101000001000000000001",
    "01000000000001000001010000000001",
)))

H18_LABELS = tuple(map(matrix, (
    "01010000000100000000010000000001",
    "01000000010100000000010000000001",
    "01000000000100000000000100000101",
    "01010000010000000000010000000001",
    "00010000010100000000010000000001",
    "01000000000100000000010100000100",
)))

# The four second-chart syllables of q_19243, in order.
Q_SECOND = tuple(map(matrix, (
    "01010000010000000000010000000001",
    "01000000010100000000010000000001",
    "00010000010100000000010000000001",
    "01010000000100000000010000000001",
)))

# The repeated first-chart syllable of q_19243.
Q_FIRST_INVOLUTION = matrix("01000000000100000000010100000001")


def main():
    h6 = subgroup(H6_LABELS)
    h18 = subgroup(H18_LABELS)
    k = subgroup(Q_SECOND)
    z = center(h18)

    assert len(h6) == 6
    assert len(h18) == 18
    assert len(k) == 6
    assert len(z) == 3
    assert k <= h18
    assert len(k & h6) == 1
    assert all(value not in h6 for value in Q_SECOND)
    assert [order(value) for value in Q_SECOND] == [3, 2, 3, 2]

    # K is the S3 direct factor of H18: its intersection with the central C3
    # is trivial and their product has all 18 elements.
    assert len(k & z) == 1
    assert len(subgroup(tuple(k | z))) == 18

    b = Q_FIRST_INVOLUTION
    assert order(b) == 2
    assert b not in h18
    assert all(commute(b, value) for value in k)

    nontrivial_z = [value for value in z if value != I4]
    assert len(nontrivial_z) == 2
    for value in nontrivial_z:
        # b conjugates the central C3 generator to its inverse.
        assert mul(mul(b, value), b) == mul(value, value)

    l = subgroup((b, nontrivial_z[0]))
    assert len(l) == 6
    assert len(center(l)) == 1
    assert len(k & l) == 1
    assert all(commute(x, y) for x in k for y in l)

    cell = subgroup(tuple(k | l))
    assert len(cell) == 36
    assert Counter(order(value) for value in cell) == Counter({2: 15, 6: 12, 3: 8, 1: 1})

    print("q_19243 second syllables generate the S3 factor K of H18=S3xC3")
    print("the repeated first-chart involution centralizes K and inverts Z(H18)=C3")
    print("therefore <H18, b> = K x <Z(H18),b> = S3 x S3 (order 36)")


if __name__ == "__main__":
    main()
