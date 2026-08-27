"""Test commutant-valued first-boundary phases in Boolean A8 modules.

The existing Boolean dual-number no-go requires all four survivor values to
be scalar.  For a representation of the universal central atlas, the exact
condition is only that they commute with both chart images.  Over the
square-zero ring this is equivalent to asking that their first-order terms
belong to the A8-commutant of the order-zero module.

This script performs that weaker, exact linear test over F_2 for the actions
of A8 on k-subsets of eight points.  When a phase survives it also extracts
one tangent matrix X giving a concrete dual-number certificate.
"""

from itertools import combinations
import json

from atlas_certified_a8_alignment import (
    CERTIFIED_REPRESENTATIVE_INDICES,
    PHASE_INDEX,
    boundary_words,
)
from atlas_certified_dual_number_certificate import (
    ALIGNMENT_KEY,
    natural_a8_map,
)
from atlas_subset_dual_central_no_go import (
    SURVIVOR_REPRESENTATIVES,
    compose,
    insert_row,
    inverse,
    reduce_row,
    subset_action,
)
from atlas_two_chart_search import factor_generators, matrix_key


def intertwiner_rows(
        linear_rows, left_permutation, right_permutation,
        left_dimension, right_dimension):
    """Rows of D -> D P_right - P_left D for a rectangular block."""
    left_inverse = inverse(left_permutation)
    rows = []
    for row_index in range(left_dimension):
        for column_index in range(right_dimension):
            right_product = linear_rows[
                right_dimension * row_index
                + right_permutation[column_index]
            ]
            left_product = linear_rows[
                right_dimension * left_inverse[row_index] + column_index
            ]
            rows.append(right_product ^ left_product)
    return rows


def word_derivative_rect_rows(
        word, represented_left, represented_right,
        alignment_left, alignment_right,
        alignment_left_inverse, alignment_right_inverse,
        left_dimension, right_dimension):
    """Rectangular block of the right-trivialized word derivative."""
    identity_left = tuple(range(left_dimension))
    identity_right = tuple(range(right_dimension))
    prefix_left = identity_left
    prefix_right = identity_right
    terms = []
    for factor, matrix in word:
        key = matrix_key(matrix).hex()
        permutation_left = represented_left[key]
        permutation_right = represented_right[key]
        if factor == 2:
            permutation_left = compose(
                compose(alignment_left_inverse, permutation_left),
                alignment_left,
            )
            permutation_right = compose(
                compose(alignment_right_inverse, permutation_right),
                alignment_right,
            )
        before_left = prefix_left
        before_right = prefix_right
        prefix_left = compose(permutation_left, prefix_left)
        prefix_right = compose(permutation_right, prefix_right)
        if factor == 2:
            terms.extend((
                (before_left, before_right),
                (prefix_left, prefix_right),
            ))
    if prefix_left != identity_left or prefix_right != identity_right:
        raise AssertionError("the inner base alignment stopped killing a word")

    rows = [0] * (left_dimension * right_dimension)
    for left_permutation, right_permutation in terms:
        for source_row in range(left_dimension):
            target_row = left_permutation[source_row]
            source_offset = right_dimension * source_row
            target_offset = right_dimension * target_row
            for source_column in range(right_dimension):
                source = source_offset + source_column
                target = target_offset + right_permutation[source_column]
                rows[target] ^= 1 << source
    return rows


def solve_affine(equations, width):
    """Solve binary linear equations given as (packed row, right side)."""
    basis = {}
    for row, right_side in equations:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (row, right_side)
                break
            other_row, other_right_side = basis[pivot]
            row ^= other_row
            right_side ^= other_right_side
        if not row and right_side:
            return None

    solution = 0
    for pivot in sorted(basis):
        row, right_side = basis[pivot]
        lower_part = row & ((1 << pivot) - 1)
        parity = (lower_part & solution).bit_count() & 1
        if parity ^ right_side:
            solution |= 1 << pivot

    for row, right_side in equations:
        if ((row & solution).bit_count() & 1) != right_side:
            raise AssertionError("binary affine solver returned a false witness")
    if solution >= 1 << width:
        raise AssertionError("affine solution exceeded the variable width")
    return solution


def subset_module(degree, images):
    subsets = tuple(combinations(range(8), degree))
    lookup = {subset: index for index, subset in enumerate(subsets)}
    represented = {
        key: subset_action(permutation, subsets, lookup)
        for key, permutation in images.items()
    }
    return {
        "degree": degree,
        "dimension": len(subsets),
        "represented": represented,
        "alignment": represented[ALIGNMENT_KEY],
        "alignment_inverse": inverse(represented[ALIGNMENT_KEY]),
    }


def analyze_block(left_module, right_module, words):
    left_degree = left_module["degree"]
    right_degree = right_module["degree"]
    left_dimension = left_module["dimension"]
    right_dimension = right_module["dimension"]
    represented_left = left_module["represented"]
    represented_right = right_module["represented"]
    selected = sorted(set(
        CERTIFIED_REPRESENTATIVE_INDICES + SURVIVOR_REPRESENTATIVES
    ))
    derivatives = {
        index: word_derivative_rect_rows(
            words[index],
            represented_left,
            represented_right,
            left_module["alignment"],
            right_module["alignment"],
            left_module["alignment_inverse"],
            right_module["alignment_inverse"],
            left_dimension,
            right_dimension,
        )
        for index in selected
    }

    represented_generators = []
    for _name, word in factor_generators()[:6]:
        key = matrix_key(word[0][1]).hex()
        represented_generators.append((
            represented_left[key], represented_right[key]
        ))

    constraint_basis = {}
    for index in CERTIFIED_REPRESENTATIVE_INDICES:
        for row in derivatives[index]:
            insert_row(constraint_basis, row)

    for index in SURVIVOR_REPRESENTATIVES:
        for left_generator, right_generator in represented_generators:
            for row in intertwiner_rows(
                derivatives[index], left_generator, right_generator,
                left_dimension, right_dimension,
            ):
                insert_row(constraint_basis, row)

    phase_rows = derivatives[PHASE_INDEX]
    phase_remainders = [
        (output_index, reduce_row(constraint_basis, row))
        for output_index, row in enumerate(phase_rows)
    ]
    surviving_outputs = [
        (output_index, remainder)
        for output_index, remainder in phase_remainders
        if remainder
    ]

    combined_basis = dict(constraint_basis)
    for row in phase_rows:
        insert_row(combined_basis, row)
    phase_image_dimension = len(combined_basis) - len(constraint_basis)

    witness = None
    if surviving_outputs:
        output_index, _remainder = surviving_outputs[0]
        equations = [(row, 0) for row in constraint_basis.values()]
        equations.append((phase_rows[output_index], 1))
        packed_solution = solve_affine(
            equations, left_dimension * right_dimension
        )
        if packed_solution is None:
            raise AssertionError("rank test found a phase but witness solve failed")
        support = [
            divmod(index, right_dimension)
            for index in range(left_dimension * right_dimension)
            if (packed_solution >> index) & 1
        ]
        witness = {
            "forced_nonzero_phase_output":
                divmod(output_index, right_dimension),
            "tangent_support": support,
            "tangent_weight": len(support),
        }

    return {
        "left_subset_degree": left_degree,
        "right_subset_degree": right_degree,
        "left_representation_dimension": left_dimension,
        "right_representation_dimension": right_dimension,
        "hom_dimension": left_dimension * right_dimension,
        "constraint_rank_over_f2": len(constraint_basis),
        "constraint_nullity_over_f2":
            left_dimension * right_dimension - len(constraint_basis),
        "phase_image_dimension_on_constraint_kernel": phase_image_dimension,
        "nonzero_commutant_valued_phase_exists": bool(surviving_outputs),
        "witness": witness,
    }


def main():
    images = natural_a8_map()
    words = boundary_words()
    modules = [subset_module(degree, images) for degree in range(1, 5)]
    records = [
        analyze_block(left_module, right_module, words)
        for left_module in modules
        for right_module in modules
    ]
    print(json.dumps({
        "coefficient_ring": "F2[eps]/(eps^2)",
        "alignment_f2_hex": ALIGNMENT_KEY,
        "certified_zero_representatives": CERTIFIED_REPRESENTATIVE_INDICES,
        "central_survivor_representatives": SURVIVOR_REPRESENTATIVES,
        "phase_representative": PHASE_INDEX,
        "centrality_condition":
            "every survivor block intertwines the first A8 chart",
        "ordered_boolean_block_records": records,
        "all_boolean_direct_sums_have_zero_phase": all(
            not record["nonzero_commutant_valued_phase_exists"]
            for record in records
        ),
        "degrees_5_6_7_follow_by_complementation": True,
    }, indent=2))


if __name__ == "__main__":
    main()
