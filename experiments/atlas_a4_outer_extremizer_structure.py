#!/usr/bin/env python3
"""Exact structure audit for the ten outer 21/4 extremizers.

This is a bounded finite-group diagnostic.  It enumerates the outer classical
A8 packet alignments, selects the positions with

    15 E_2HOL = 84,   15 ||q_19243-I||_2^2 = 16,

and records exact conjugacy, generated-subgroup, and short normal-generation
data for the collision and the two bridge cocycles.
"""

import collections
import json
import os

import numpy as np

from atlas_a4_classical_two_holonomy_profile import (
    bridge_labels,
    defect_numerator,
    outer,
    transformed,
    word_value,
)
from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


def order(matrix):
    value = I4.copy()
    for exponent in range(1, 64):
        value = gf2_mul(value, matrix)
        if matrix_key(value) == matrix_key(I4):
            return exponent
    raise AssertionError("matrix order exceeded GL4 bound")


def subgroup_order(generators):
    identity = matrix_key(I4)
    seen = {identity: I4.copy()}
    queue = collections.deque([I4.copy()])
    while queue:
        value = queue.popleft()
        for generator in generators:
            product = gf2_mul(value, generator)
            key = matrix_key(product)
            if key not in seen:
                seen[key] = product
                queue.append(product)
    return len(seen)


def conjugacy_class(matrix, group):
    values = {}
    for conjugator in group:
        value = gf2_mul(gf2_mul(conjugator, matrix), gf2_inv(conjugator))
        values[matrix_key(value)] = value
    return values


def normal_length_at_most_four(target, conjugates):
    target_key = matrix_key(target)
    identity = matrix_key(I4)
    if target_key == identity:
        return 0
    if target_key in conjugates:
        return 1

    values = list(conjugates.values())
    pair_products = {}
    for left in values:
        needed = gf2_mul(gf2_inv(left), target)
        if matrix_key(needed) in conjugates:
            return 2
        for right in values:
            product = gf2_mul(left, right)
            pair_products[matrix_key(product)] = product

    for product in pair_products.values():
        needed = gf2_mul(gf2_inv(product), target)
        if matrix_key(needed) in conjugates:
            return 3
    for product in pair_products.values():
        needed = gf2_mul(gf2_inv(product), target)
        if matrix_key(needed) in pair_products:
            return 4
    return None


def invariant_tuple(matrix):
    return {
        "hex": matrix_key(matrix).hex(),
        "order": order(matrix),
        "defect_numerator_over_15": defect_numerator(matrix),
    }


def main():
    group = list(enumerate_gl4())
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])

    c, a = bridge_labels()
    identity = matrix_key(I4)
    records = []
    for alignment in group:
        inverse = gf2_inv(alignment)
        if not all(
            matrix_key(word_value(word, alignment, inverse, True)) == identity
            for _index, word in packet
        ):
            continue
        q_value = word_value(collision, alignment, inverse, True)
        c_cocycle = gf2_mul(transformed(c, alignment, inverse, True), gf2_inv(c))
        a_cocycle = gf2_mul(transformed(a, alignment, inverse, True), gf2_inv(a))
        q_num = defect_numerator(q_value)
        energy_num = 2 * defect_numerator(c_cocycle) + defect_numerator(a_cocycle)
        if (energy_num, q_num) != (84, 16):
            continue

        q_conjugates = conjugacy_class(q_value, group)
        products = {
            "c_times_a": gf2_mul(c_cocycle, a_cocycle),
            "a_times_c": gf2_mul(a_cocycle, c_cocycle),
            "commutator": gf2_mul(
                gf2_mul(gf2_mul(c_cocycle, a_cocycle), gf2_inv(c_cocycle)),
                gf2_inv(a_cocycle),
            ),
        }
        records.append({
            "alignment_hex": matrix_key(alignment).hex(),
            "q": invariant_tuple(q_value),
            "c_cocycle": invariant_tuple(c_cocycle),
            "a_cocycle": invariant_tuple(a_cocycle),
            "products": {name: invariant_tuple(value) for name, value in products.items()},
            "q_conjugacy_class_size": len(q_conjugates),
            "normal_q_length": {
                "c_cocycle": normal_length_at_most_four(c_cocycle, q_conjugates),
                "a_cocycle": normal_length_at_most_four(a_cocycle, q_conjugates),
            },
            "generated_subgroup_order": subgroup_order([q_value, c_cocycle, a_cocycle]),
        })

    if len(records) != 10:
        raise AssertionError("outer extremizer count changed: %d" % len(records))
    print(json.dumps({"outer_21_over_4_extremizers": records}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
