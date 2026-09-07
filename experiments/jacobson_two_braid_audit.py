#!/usr/bin/env python3
"""Exact finite checks for the Jacobson two-braid reduction.

Uses only integer arithmetic. The exhaustive search covers the specified
six-dimensional natural module over F_2, not arbitrary unitary dimensions.
The 56-point packet checks necessary constraints; no extension H is claimed.
"""

import json
from itertools import product


def identity(n):
    """Column encoding of an F_2 matrix."""
    return tuple(1 << i for i in range(n))


def apply(a, vector):
    out = 0
    while vector:
        bit = vector & -vector
        out ^= a[bit.bit_length() - 1]
        vector ^= bit
    return out


def multiply(a, b):
    return tuple(apply(a, column) for column in b)


def power(a, exponent):
    out = identity(len(a))
    for _ in range(exponent):
        out = multiply(out, a)
    return out


def swap(n, i, j):
    out = list(identity(n))
    out[i], out[j] = out[j], out[i]
    return tuple(out)


def transvection(n, i, j):
    out = list(identity(n))
    out[j] ^= 1 << i
    return tuple(out)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def closure(generators, n):
    seen = {identity(n)}
    todo = [identity(n)]
    while todo:
        a = todo.pop()
        for g in generators:
            b = multiply(g, a)
            if b not in seen:
                seen.add(b)
                todo.append(b)
    return seen


def natural_six_search():
    n = 6
    one = identity(n)
    u = multiply(swap(n, 0, 1), swap(n, 3, 4))
    b = multiply(swap(n, 1, 2), swap(n, 4, 5))
    dp = swap(n, 3, 5)
    c = swap(n, 1, 2)
    rho = multiply(u, b)
    rho2 = power(rho, 2)
    conjugator = multiply(c, rho2)
    conjugator_inverse = multiply(rho, c)
    active = (1, 3, 4, 5)
    counts = {"involutions": 0, "affine_braid": 0,
              "tail_braid": 0, "joint_braids": 0,
              "relator_identities_checked": 0}
    # Every 4 by 4 matrix occurs once; its square being I implies invertibility.
    for small in product(range(16), repeat=4):
        if power(small, 2) != identity(4):
            continue
        counts["involutions"] += 1
        h = list(one)
        for j, ambient_j in enumerate(active):
            h[ambient_j] = sum(1 << active[i] for i in range(4)
                               if small[j] & (1 << i))
        h = tuple(h)
        affine = power(multiply(h, b), 3)
        tail = power(multiply(h, dp), 3)
        counts["affine_braid"] += int(affine == one)
        counts["tail_braid"] += int(tail == one)
        counts["joint_braids"] += int(affine == one and tail == one)
        a = multiply(h, u)
        a23 = multiply(multiply(rho, a), rho2)
        a31 = multiply(multiply(rho2, a), rho)
        old_relator = multiply(multiply(multiply(a31, a23), a), c)
        new_relator = multiply(multiply(conjugator, tail), conjugator_inverse)
        require(old_relator == new_relator, "Controlled-relator identity failed")
        counts["relator_identities_checked"] += 1
    require(counts["involutions"] == 316, "Unexpected involution count")
    require(counts["affine_braid"] == 12, "Unexpected affine-braid count")
    require(counts["joint_braids"] == 0, "A natural joint model was found")
    return {"field": 2, "dimension": 6,
            "scope": "One natural head and one natural tail module; all K-central involutions",
            **counts}


def finite_packet():
    one = identity(3)
    group = sorted(a for a in product(range(8), repeat=3)
                   if len({apply(a, v) for v in range(8)}) == 8)
    require(len(group) == 168, "GL_3(2) enumeration failed")
    singer = next(a for a in group if a != one and power(a, 7) == one)
    normalizer = next(a for a in group if a != one and power(a, 3) == one
                      and multiply(a, singer) == multiply(power(singer, 2), a))
    subgroup = closure((singer, normalizer), 3)
    require(len(subgroup) == 21, "The odd-order subgroup has wrong size")
    cosets = []
    coset_of = {}
    for g in group:
        if g in coset_of:
            continue
        coset = {multiply(g, h) for h in subgroup}
        require(not (coset & set(coset_of)), "Cosets overlap")
        index = len(cosets)
        cosets.append((g, coset))
        for member in coset:
            coset_of[member] = index
    require(len(cosets) == 8, "Expected eight tail cosets")
    natural = {g: tuple(apply(g, v) - 1 for v in range(1, 8)) for g in group}
    tail = {g: tuple(coset_of[multiply(g, rep)] for rep, _ in cosets) for g in group}
    # Replay the entire action table, independently of the coset construction.
    for g in group:
        require(sorted(tail[g]) == list(range(8)), "Tail action is not a permutation")
        for h in group:
            gh = multiply(g, h)
            require(tail[gh] == tuple(tail[g][tail[h][i]] for i in range(8)),
                    "Tail action is not a group homomorphism")
    require(len(set(tail.values())) == 168, "Tail action is not faithful")

    def fixed(g, h):
        # The product action is on the 7 x 8 pairs, evaluated directly.
        return sum(natural[g][i] == i and tail[h][j] == j
                   for i in range(7) for j in range(8))

    t = transvection(3, 0, 2)
    d = swap(3, 0, 2)
    b = swap(3, 1, 2)
    dimension = 56
    marked_rank = (dimension - fixed(t, one)) // 2
    tail_rank = (dimension - fixed(one, d)) // 2
    product_rank = (dimension - fixed(b, b)) // 2
    joint_numerator = dimension - fixed(t, one) - fixed(one, b) + fixed(t, b)
    require(joint_numerator % 4 == 0, "Invalid joint eigenspace numerator")
    joint_negative = joint_numerator // 4

    row_group = [multiply(power(transvection(3, 0, 1), a & 1),
                          power(transvection(3, 0, 2), (a >> 1) & 1))
                 for a in range(4)]

    def character(index, element):
        return (-1) ** ((index & element).bit_count())

    multiplicities = []
    for alpha in range(4):
        row = []
        for beta in range(4):
            numerator = sum(character(alpha, a) * character(beta, b0)
                            * fixed(row_group[a], row_group[b0])
                            for a in range(4) for b0 in range(4))
            require(numerator >= 0 and numerator % 16 == 0,
                    "Invalid character multiplicity")
            row.append(numerator // 16)
        multiplicities.append(row)
    require((marked_rank, tail_rank, product_rank, joint_negative) == (16, 28, 28, 8),
            "Unexpected product-packet rank data")
    require(multiplicities == [[8] * 4] + [[2] * 4 for _ in range(3)],
            "Unexpected four-group multiplicity table")
    return {"dimension": dimension, "head_action_degree": 7,
            "tail_action_degree": 8, "tail_stabilizer_order": 21,
            "tail_action_products_verified": len(group) ** 2,
            "marked_negative_rank": marked_rank, "tail_negative_rank": tail_rank,
            "head_tail_product_negative_rank": product_rank,
            "joint_negative_rank": joint_negative,
            "four_group_multiplicities": multiplicities,
            "k": 2, "extension_involution_constructed": False,
            "scope": "Exact finite packet satisfying necessary rank constraints only"}


def run():
    return {"format": "jacobson-two-braid-audit-v1",
            "arithmetic": "Exact integers and F_2; no floating point",
            "natural_six": natural_six_search(),
            "mixed_packet": finite_packet(),
            "positive_all_dimensions_gap_proved": False,
            "non_mf_existence_proved": False}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
