"""Exhaust classical A8 alignments for the certified atlas package.

The 178 radius-five perfect-overlap certificates collapse to 24 cyclic
classes.  A homomorphism from either simple A8 factor to A8 is trivial or an
automorphism.  Every automorphism of GL(4,2) ~= A8 is inner, or inner after
the outer involution ``g -> (g^-1)^T``.  This script exhausts those 40,320
nontrivial/nontrivial alignments and the two one-factor cases, asking whether
all 24 certified classes can vanish while phase class 11 survives.
"""

import json

import numpy as np

from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import (
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


CERTIFIED_REPRESENTATIVE_INDICES = (
    0, 2, 10, 13, 16, 17, 35, 50, 65, 68, 70, 72,
    80, 86, 90, 91, 114, 125, 126, 127, 218, 221, 224, 227,
)
PHASE_INDEX = 11


def boundary_words():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    identity_key = matrix_key(I4)
    boundary = [word for word in words if any(
        matrix_key(projection) != identity_key
        for projection in factor_projections(word))]
    if len(boundary) != 234:
        raise AssertionError("complete boundary changed")
    return boundary


def outer(matrix):
    return gf2_inv(matrix).T.copy()


def aligned_value(word, alignment, alignment_inverse, use_outer):
    value = I4.copy()
    for factor, matrix in word:
        image = matrix
        if factor == 2:
            if use_outer:
                image = outer(image)
            image = gf2_mul(gf2_mul(
                alignment, image), alignment_inverse)
        value = gf2_mul(value, image)
    return matrix_key(value)


def one_factor_value(word, selected_factor):
    value = I4.copy()
    for factor, matrix in word:
        if factor == selected_factor:
            value = gf2_mul(value, matrix)
    return matrix_key(value)


def matrix_order_from_key(key):
    value = np.frombuffer(key, dtype=np.uint8).reshape(4, 4)
    power = I4.copy()
    for exponent in range(1, 16):
        power = gf2_mul(power, value)
        if matrix_key(power) == matrix_key(I4):
            return exponent
    raise AssertionError("GL(4,2) element order exceeded 15")


def scan_automorphism_coset(words, phase, use_outer):
    identity_key = matrix_key(I4)
    solutions = []
    best = -1
    best_count = 0
    for alignment in enumerate_gl4():
        alignment_inverse = gf2_inv(alignment)
        killed = 0
        for word in words:
            if (aligned_value(
                    word, alignment, alignment_inverse, use_outer)
                    == identity_key):
                killed += 1
            else:
                break
        if killed > best:
            best = killed
            best_count = 1
        elif killed == best:
            best_count += 1
        if killed != len(words):
            continue
        phase_image = aligned_value(
            phase, alignment, alignment_inverse, use_outer)
        solutions.append({
            "alignment_f2_hex": matrix_key(alignment).hex(),
            "phase_f2_hex": phase_image.hex(),
            "phase_survives": phase_image != identity_key,
            "phase_order": matrix_order_from_key(phase_image),
        })
    return {
        "automorphism_coset": "outer" if use_outer else "inner",
        "alignments_tested": 20160,
        "certified_relators": len(words),
        "solutions": len(solutions),
        "phase_surviving_solutions": sum(
            solution["phase_survives"] for solution in solutions),
        "solution_records": solutions,
        "longest_initial_relator_prefix_killed": best,
        "alignments_at_best_prefix": best_count,
    }


def main():
    boundary = boundary_words()
    certified = [
        boundary[index] for index in CERTIFIED_REPRESENTATIVE_INDICES]
    phase = boundary[PHASE_INDEX]
    identity_key = matrix_key(I4)
    one_factor = []
    for selected_factor in (1, 2):
        kills_certified = all(
            one_factor_value(word, selected_factor) == identity_key
            for word in certified)
        phase_image = one_factor_value(phase, selected_factor)
        one_factor.append({
            "selected_factor": selected_factor,
            "kills_all_certified": kills_certified,
            "phase_f2_hex": phase_image.hex(),
            "phase_survives": phase_image != identity_key,
            "phase_order": matrix_order_from_key(phase_image),
        })
    print(json.dumps({
        "certified_representative_indices":
            CERTIFIED_REPRESENTATIVE_INDICES,
        "phase_index": PHASE_INDEX,
        "one_factor_cases": one_factor,
        "automorphism_cases": [
            scan_automorphism_coset(certified, phase, False),
            scan_automorphism_coset(certified, phase, True),
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
