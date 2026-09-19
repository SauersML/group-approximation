"""Test second-order Boolean phases in the natural eight-point A8 module.

Work over F_2[eps]/(eps^3) with relative alignment

    (I + eps X + eps^2 Y) sigma(h).

The first-order certified-zero and survivor-centrality equations have a
three-dimensional kernel.  This script exhausts its eight elements.  For
each X it forms the exact affine equations on Y at order eps^2 and tests
whether survivor 11 can be nonzero while all 24 certified words vanish and
all four survivors commute with the first A8 chart.
"""

import json

import numpy as np

from atlas_certified_a8_alignment import (
    CERTIFIED_REPRESENTATIVE_INDICES,
    PHASE_INDEX,
    boundary_words,
)
from atlas_certified_dual_number_certificate import (
    ALIGNMENT_KEY,
    f2_mul,
    natural_a8_map,
    permutation_matrix,
)
from atlas_subset_dual_central_no_go import (
    SURVIVOR_REPRESENTATIVES,
    insert_row,
)
from atlas_subset_dual_commutant_phase import (
    intertwiner_rows,
    solve_affine,
    subset_module,
    word_derivative_rect_rows,
)
from atlas_two_chart_search import factor_generators, matrix_key


def triple_mul(left, right):
    a0, a1, a2 = left
    b0, b1, b2 = right
    return (
        f2_mul(a0, b0),
        f2_mul(a0, b1) ^ f2_mul(a1, b0),
        f2_mul(a0, b2) ^ f2_mul(a1, b1) ^ f2_mul(a2, b0),
    )


def chart_triples(module, tangent):
    dimension = module["dimension"]
    identity = np.eye(dimension, dtype=np.uint8)
    zero = np.zeros((dimension, dimension), dtype=np.uint8)
    alignment = permutation_matrix(module["alignment"])
    alignment_inverse = alignment.T.copy()
    tangent_square = f2_mul(tangent, tangent)
    left_alignment = (
        alignment,
        f2_mul(tangent, alignment),
        zero,
    )
    right_alignment = (
        alignment_inverse,
        f2_mul(alignment_inverse, tangent),
        f2_mul(alignment_inverse, tangent_square),
    )
    first = {}
    second = {}
    for key, permutation in module["represented"].items():
        value = permutation_matrix(permutation)
        first[key] = (value, zero, zero)
        second[key] = triple_mul(
            triple_mul(left_alignment, (value, zero, zero)),
            right_alignment,
        )
    return first, second, identity, zero


def evaluate(word, first, second, identity, zero):
    value = (identity, zero, zero)
    for factor, matrix in word:
        chart = first if factor == 1 else second
        value = triple_mul(value, chart[matrix_key(matrix).hex()])
    return value


def kernel_basis(equation_basis, width):
    pivots = set(equation_basis)
    free_variables = [index for index in range(width) if index not in pivots]
    result = []
    for free_variable in free_variables:
        vector = 1 << free_variable
        for pivot in sorted(pivots):
            row = equation_basis[pivot]
            lower = row & ((1 << pivot) - 1)
            if (lower & vector).bit_count() & 1:
                vector |= 1 << pivot
        for row in equation_basis.values():
            if (row & vector).bit_count() & 1:
                raise AssertionError("kernel basis construction failed")
        result.append(vector)
    return result


def packed_matrix(packed, dimension):
    result = np.zeros((dimension, dimension), dtype=np.uint8)
    for index in range(dimension * dimension):
        if (packed >> index) & 1:
            row, column = divmod(index, dimension)
            result[row, column] = 1
    return result


def packed_entries(matrix):
    result = 0
    dimension = matrix.shape[1]
    for row in range(matrix.shape[0]):
        for column in range(dimension):
            if matrix[row, column]:
                result |= 1 << (dimension * row + column)
    return result


def main():
    images = natural_a8_map()
    words = boundary_words()
    module = subset_module(1, images)
    dimension = module["dimension"]
    width = dimension * dimension
    selected = sorted(set(
        CERTIFIED_REPRESENTATIVE_INDICES + SURVIVOR_REPRESENTATIVES
    ))
    derivatives = {
        index: word_derivative_rect_rows(
            words[index],
            module["represented"], module["represented"],
            module["alignment"], module["alignment"],
            module["alignment_inverse"], module["alignment_inverse"],
            dimension, dimension,
        )
        for index in selected
    }
    generators = []
    for _name, word in factor_generators()[:6]:
        generators.append(
            module["represented"][matrix_key(word[0][1]).hex()]
        )

    homogeneous_basis = {}
    for index in CERTIFIED_REPRESENTATIVE_INDICES:
        for row in derivatives[index]:
            insert_row(homogeneous_basis, row)
    for index in SURVIVOR_REPRESENTATIVES:
        for generator in generators:
            for row in intertwiner_rows(
                    derivatives[index], generator, generator,
                    dimension, dimension):
                insert_row(homogeneous_basis, row)

    nullspace = kernel_basis(homogeneous_basis, width)
    if len(nullspace) != 3:
        raise AssertionError("natural-module first-order nullity changed")

    records = []
    for mask in range(1 << len(nullspace)):
        packed_tangent = 0
        for index, vector in enumerate(nullspace):
            if (mask >> index) & 1:
                packed_tangent ^= vector
        tangent = packed_matrix(packed_tangent, dimension)
        tangent_in_chart_commutant = all(
            np.array_equal(
                f2_mul(tangent, permutation_matrix(generator)),
                f2_mul(permutation_matrix(generator), tangent),
            )
            for generator in generators
        )
        first, second, identity, zero = chart_triples(module, tangent)
        quadratic = {
            index: evaluate(
                words[index], first, second, identity, zero
            )[2]
            for index in selected
        }

        affine_equations = []
        for index in CERTIFIED_REPRESENTATIVE_INDICES:
            right_sides = packed_entries(quadratic[index])
            for output_index, row in enumerate(derivatives[index]):
                affine_equations.append((
                    row, (right_sides >> output_index) & 1
                ))
        for index in SURVIVOR_REPRESENTATIVES:
            for generator in generators:
                commutator_constant = packed_entries(
                    f2_mul(quadratic[index], permutation_matrix(generator))
                    ^ f2_mul(permutation_matrix(generator), quadratic[index])
                )
                rows = intertwiner_rows(
                    derivatives[index], generator, generator,
                    dimension, dimension,
                )
                for output_index, row in enumerate(rows):
                    affine_equations.append((
                        row, (commutator_constant >> output_index) & 1
                    ))

        packed_second_tangent = solve_affine(affine_equations, width)
        if packed_second_tangent is None:
            if tangent_in_chart_commutant:
                raise AssertionError("a chart-commutant tangent was obstructed")
            records.append({
                "first_order_mask": mask,
                "first_order_tangent_weight": int(tangent.sum()),
                "first_order_tangent_in_chart_commutant":
                    tangent_in_chart_commutant,
                "second_order_extension_exists": False,
                "second_order_phase_is_nonzero": False,
            })
            continue

        phase_linear = 0
        for output_index, row in enumerate(derivatives[PHASE_INDEX]):
            if (row & packed_second_tangent).bit_count() & 1:
                phase_linear |= 1 << output_index
        phase_quadratic = packed_entries(quadratic[PHASE_INDEX])
        phase = phase_linear ^ phase_quadratic
        if not tangent_in_chart_commutant:
            raise AssertionError("a noncommutant tangent extended to order two")
        records.append({
            "first_order_mask": mask,
            "first_order_tangent_weight": int(tangent.sum()),
            "first_order_tangent_in_chart_commutant":
                tangent_in_chart_commutant,
            "second_order_extension_exists": True,
            "second_order_phase_is_nonzero": bool(phase),
            "second_order_phase_weight": phase.bit_count(),
        })

    print(json.dumps({
        "coefficient_ring": "F2[eps]/(eps^3)",
        "module": "natural eight-point permutation module",
        "first_order_constraint_rank": len(homogeneous_basis),
        "first_order_constraint_nullity": len(nullspace),
        "first_order_tangents_exhausted": len(records),
        "records": records,
        "nonzero_second_order_phase_exists": any(
            record["second_order_phase_is_nonzero"]
            for record in records
        ),
    }, indent=2))


if __name__ == "__main__":
    main()
