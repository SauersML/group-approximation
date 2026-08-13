"""Find degree-one synchronization equations after exact H alignment.

Use the left-trivialized convention

    U = W lambda(k0)

at the unique classical boundary alignment and assume ``W`` commutes with
``H=diag(GL(3,2),1)``.  A second-chart syllable whose
aligned group element lies in ``H`` then loses its two surrounding ``W``
factors.  If a collision word contains exactly one transverse second-chart
syllable, its value has the form

    lambda(A) W lambda(B) W* lambda(C).

The true relation therefore asks for the degree-one equation

    W lambda(B) W* = lambda(A^-1 C^-1).

This script extracts every such equation from the complete radius-five
collision tree.  Two different targets for the same ``B`` would give an
immediate fixed Hilbert--Schmidt obstruction once the boundary has been
H-exactified.
"""

import argparse
import json
from collections import Counter, defaultdict

import numpy as np

from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_kernel_collision_enumerator import (
    enumerate_ball,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key
from atlas_two_chart_search import factor_generators


def lies_in_h(matrix):
    expected = I4.copy()
    expected[:3, :3] = matrix[:3, :3]
    return np.array_equal(matrix, expected)


def aligned_matrix(factor, matrix, alignment, alignment_inverse):
    if factor == 1:
        return matrix
    return gf2_mul(gf2_mul(alignment, matrix), alignment_inverse)


def aligned_value(word, alignment, alignment_inverse):
    value = I4.copy()
    for factor, element in word:
        value = gf2_mul(value, aligned_matrix(
            factor, element, alignment, alignment_inverse))
    return value


def single_bridge_equation(word, alignment, alignment_inverse):
    represented = [
        (factor, aligned_matrix(
            factor, element, alignment, alignment_inverse))
        for factor, element in word
    ]
    transverse = [index for index, (factor, element) in enumerate(represented)
                  if factor == 2 and not lies_in_h(element)]
    if len(transverse) != 1:
        return None
    pivot = transverse[0]
    left = I4.copy()
    right = I4.copy()
    for _factor, element in represented[:pivot]:
        left = gf2_mul(left, element)
    bridge = represented[pivot][1]
    for _factor, element in represented[pivot + 1:]:
        right = gf2_mul(right, element)
    target = gf2_mul(gf2_inv(left), gf2_inv(right))
    return bridge, target


def matrix_order(matrix):
    power = I4.copy()
    for exponent in range(1, 16):
        power = gf2_mul(power, matrix)
        if np.array_equal(power, I4):
            return exponent
    raise AssertionError("element order exceeds GL(4,2) maximum")


def first_noncommuting_factor_one_generator(value):
    for name, word in factor_generators()[:6]:
        generator = word[0][1]
        commutator_value = gf2_mul(gf2_mul(
            gf2_mul(generator, value), gf2_inv(generator)),
            gf2_inv(value))
        if not np.array_equal(commutator_value, I4):
            return name, commutator_value
    raise AssertionError("nonidentity A8 element commutes with all generators")


def run(radius=5):
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    states, sphere_sizes = enumerate_ball(radius)
    words, _, _ = spanning_tree_kernel_words(states)
    equations = []
    target_by_bridge = defaultdict(set)
    transverse_second_histogram = Counter()
    failed_transverse_second_histogram = Counter()
    fixed_h_commutant_failures = []
    failed = 0
    for index, word in enumerate(words):
        transverse_second = sum(
            factor == 2 and not lies_in_h(aligned_matrix(
                factor, element, alignment, alignment_inverse))
            for factor, element in word)
        transverse_second_histogram[transverse_second] += 1
        word_fails = not np.array_equal(aligned_value(
            word, alignment, alignment_inverse), I4)
        if word_fails:
            failed += 1
            failed_transverse_second_histogram[transverse_second] += 1
            if transverse_second == 0:
                value = aligned_value(
                    word, alignment, alignment_inverse)
                generator_name, commutator_value = (
                    first_noncommuting_factor_one_generator(value))
                fixed_h_commutant_failures.append({
                    "word_index": index,
                    "aligned_value_hex": matrix_key(value).hex(),
                    "aligned_value_order": matrix_order(value),
                    "word_length": len(word),
                    "factor_one_generator": generator_name,
                    "commutator_value_hex": matrix_key(
                        commutator_value).hex(),
                    "commutator_value_order": matrix_order(
                        commutator_value),
                    "normalized_hs_defect": 2 ** 0.5,
                })
        equation = single_bridge_equation(
            word, alignment, alignment_inverse)
        if equation is None:
            continue
        bridge, target = equation
        bridge_key = matrix_key(bridge).hex()
        target_key = matrix_key(target).hex()
        target_by_bridge[bridge_key].add(target_key)
        equations.append({
            "word_index": index,
            "bridge_hex": bridge_key,
            "target_hex": target_key,
            "bridge_equals_target": bridge_key == target_key,
            "bridge_order": matrix_order(bridge),
            "target_order": matrix_order(target),
        })
    conflicts = {
        bridge: sorted(targets)
        for bridge, targets in target_by_bridge.items() if len(targets) > 1
    }
    return {
        "radius": radius,
        "sphere_sizes": sphere_sizes,
        "collision_tree_words": len(words),
        "classical_alignment_failures": failed,
        "transverse_second_syllable_histogram": sorted(
            transverse_second_histogram.items()),
        "failed_transverse_second_syllable_histogram": sorted(
            failed_transverse_second_histogram.items()),
        "fixed_h_commutant_failures": fixed_h_commutant_failures,
        "single_transverse_second_chart_equations": len(equations),
        "distinct_bridges": len(target_by_bridge),
        "equations_with_commuting_target": sum(
            record["bridge_equals_target"] for record in equations),
        "bridges_with_multiple_targets": len(conflicts),
        "target_multiplicity_histogram": sorted(Counter(
            len(targets) for targets in target_by_bridge.values()).items()),
        "conflicts": conflicts,
        "equations": equations,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=5)
    args = parser.parse_args()
    if args.radius < 0:
        raise ValueError("radius must be nonnegative")
    print(json.dumps(run(args.radius), indent=2))
