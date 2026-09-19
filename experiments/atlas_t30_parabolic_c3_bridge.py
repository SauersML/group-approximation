#!/usr/bin/env python3
"""Exact P--C3--P bridge for the transverse transvection t30.

The A4 packet/collision subgroup ladder gives a hyperplane stabilizer

    P = <H6, K, b> < GL(4,2)

and a central order-three element z of H18 outside P.  Since GL(4,2) acts
2-transitively on the fifteen nonzero covectors, P has only two double
cosets.  This audit finds an explicit shortest factorization

    t30 = p_left z^sign p_right

and records short words for the two parabolic factors in the packet/collision
generators.  Everything is exact over F2.
"""

import json
from collections import deque

from atlas_a4_19243_component_localization import (
    H6_LABELS,
    H18_LABELS,
    I4,
    Q_FIRST_INVOLUTION,
    Q_SECOND,
    center,
    mul,
    order,
    subgroup,
)


def transvection(row, col):
    return tuple(tuple(
        int(i == j) ^ int(i == row and j == col)
        for j in range(4)) for i in range(4))


def power(a, exponent):
    value = I4
    for _ in range(exponent):
        value = mul(value, a)
    return value


def inverse(a):
    return power(a, order(a) - 1)


def matrix_hex(a):
    return bytes(entry for row in a for entry in row).hex()


def named_generators():
    raw = []
    for index, value in enumerate(H6_LABELS):
        raw.append(("h6_%d" % index, value))
    for index, value in enumerate(Q_SECOND):
        raw.append(("k_%d" % index, value))
    raw.append(("b", Q_FIRST_INVOLUTION))

    out = []
    seen = set()
    for name, value in raw:
        if value not in seen:
            out.append((name, value))
            seen.add(value)
        value_inv = inverse(value)
        if value_inv not in seen:
            out.append((name + "^-1", value_inv))
            seen.add(value_inv)
    return out


def shortest_words(generators):
    words = {I4: ()}
    queue = deque([I4])
    while queue:
        old = queue.popleft()
        for name, generator in generators:
            new = mul(old, generator)
            if new not in words:
                words[new] = words[old] + (name,)
                queue.append(new)
    return words


def main():
    generators = named_generators()
    words = shortest_words(generators)
    p = subgroup(tuple(H6_LABELS) + tuple(Q_SECOND) + (Q_FIRST_INVOLUTION,))
    assert set(words) == p
    assert len(p) == 1344

    h18 = subgroup(H18_LABELS)
    zs = sorted((value for value in center(h18) if value != I4), key=matrix_hex)
    assert len(zs) == 2
    assert zs[1] == inverse(zs[0])

    target = transvection(3, 0)
    assert target not in p

    candidates = []
    for z_index, z in enumerate(zs):
        z_inv = inverse(z)
        for p_left in p:
            # target = p_left z p_right.
            p_right = mul(mul(z_inv, inverse(p_left)), target)
            if p_right in p:
                candidates.append((
                    len(words[p_left]) + len(words[p_right]),
                    len(words[p_left]),
                    len(words[p_right]),
                    z_index,
                    words[p_left],
                    words[p_right],
                    p_left,
                    p_right,
                ))

    assert candidates
    candidates.sort(key=lambda item: item[:7])
    best = candidates[0]
    _, left_length, right_length, z_index, left_word, right_word, p_left, p_right = best
    z = zs[z_index]
    assert mul(mul(p_left, z), p_right) == target
    assert left_length + right_length == 5
    assert left_word == ("k_0^-1", "h6_2^-1")
    assert right_word == ("b", "h6_2", "k_0")

    h = H6_LABELS[2]
    k = Q_SECOND[0]
    c = mul(h, k)
    a = mul(z, Q_FIRST_INVOLUTION)
    assert order(c) == 4
    assert order(a) == 2
    assert p_left == inverse(c)
    assert p_right == mul(Q_FIRST_INVOLUTION, c)
    assert mul(mul(inverse(c), z), mul(Q_FIRST_INVOLUTION, c)) == target
    assert mul(mul(inverse(c), a), c) == target

    # Double-coset cardinality is |P|^2/|P intersect zPz^-1|.  This avoids an
    # unnecessary quadratic enumeration of PzP.
    z_inv = inverse(z)
    conjugate_p = {mul(mul(z, value), z_inv) for value in p}
    intersection_order = len(p & conjugate_p)
    nontrivial_double_coset_order = len(p) * len(p) // intersection_order
    assert z not in p
    assert intersection_order == 96
    assert nontrivial_double_coset_order == 20160 - 1344

    print(json.dumps({
        "ambient_group_order": 20160,
        "parabolic_order": len(p),
        "parabolic_conjugate_intersection_order": intersection_order,
        "nontrivial_double_coset_order": nontrivial_double_coset_order,
        "z_hex": matrix_hex(z),
        "z_order": order(z),
        "t30_hex": matrix_hex(target),
        "p_left_hex": matrix_hex(p_left),
        "p_right_hex": matrix_hex(p_right),
        "p_left_word": list(left_word),
        "p_right_word": list(right_word),
        "parabolic_word_length_sum": left_length + right_length,
        "factorization": "t30 = p_left z p_right",
        "compressed_factorization": "t30 = (h6_2 k_0)^-1 z b (h6_2 k_0)",
        "two_holonomy_factorization": "t30 = c^-1 a c, c=h6_2 k_0, a=z b",
        "c_hex": matrix_hex(c),
        "c_order": order(c),
        "a_hex": matrix_hex(a),
        "a_order": order(a),
        "weighted_coordinate_energy": "2 delta(h6_2)^2 + 2 delta(k_0)^2 + delta(z)^2 + delta(b)^2",
        "root_energy_bound": "x30^2 <= 3 weighted_coordinate_energy",
        "two_holonomy_energy": "2 delta(c)^2 + delta(a)^2",
        "two_holonomy_euclidean_bound": "x30^2 <= (3/2) two_holonomy_energy",
        "covariance_bridge": (
            "||[U,rho(t30)]||_2 <= ||[U,rho(p_left)]||_2 "
            "+ ||[U,rho(z)]||_2 + ||[U,rho(p_right)]||_2"
        ),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
