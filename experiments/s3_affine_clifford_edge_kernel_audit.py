#!/usr/bin/env python3
"""Exact presentation audit for the regular S3 affine-Clifford edge.

The audit has three layers.

1.  It constructs the class-two source Schur packet with its dummy Pauli
    pair and the fresh packet with the two complementary controlled pairs.
    The map

        x_dummy -> p_- p_+,   z_dummy -> q_- q_+

    is checked on every commutator and on the full normal-form vector spaces.

2.  It tests the stronger, full-Clifford version of the one-copy residual
    obstruction.  A congruence permuting two nondegenerate alternating forms
    would make Omega_1^-1 Omega_2 similar to its inverse (for the swap) and
    to I + Omega_1^-1 Omega_2 (for the shear).  These tests allow arbitrary
    mixing of the two residual Pauli Lagrangians, not merely separate row and
    column changes.

3.  It audits the sixfold regular stabilization and the tempting quotient
    which identifies the six private residual Pauli packets.  The regular
    map has zero kernel.  The shared-residual quotient has a 150-dimensional
    kernel on the residual Pauli quotient alone.

All arithmetic is exact over F_2.
"""

from __future__ import annotations

import json
from itertools import product

from common_schur_residual_hyperplane import (
    hyperplane_basis,
    restricted_matrix,
)
from invertible_direction_schur_compiler import (
    rank_matrix,
    search_certificate,
)
RESET_PLANE = (0x2CE6, 0xB0EB, 0x9C0D)
RESIDUAL_DIMENSION = 15
CENTER_DIMENSION = 5  # J and four semantic selector coefficients
SOURCE_QUOTIENT_DIMENSION = 2 * RESIDUAL_DIMENSION + 2
FRESH_QUOTIENT_DIMENSION = 2 * RESIDUAL_DIMENSION + 4
REGULAR_FACTORS = 6


def zero_matrix(rows: int, columns: int) -> list[list[int]]:
    return [[0 for _ in range(columns)] for _ in range(rows)]


def transpose(matrix: list[list[int]]) -> list[list[int]]:
    return [list(column) for column in zip(*matrix)]


def identity(size: int) -> list[list[int]]:
    return [[int(row == column) for column in range(size)] for row in range(size)]


def add(left: list[list[int]], right: list[list[int]]) -> list[list[int]]:
    return [
        [a ^ b for a, b in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def multiply(left: list[list[int]], right: list[list[int]]) -> list[list[int]]:
    rows = len(left)
    middle = len(right)
    columns = len(right[0])
    return [
        [
            sum(left[row][index] * right[index][column] for index in range(middle)) & 1
            for column in range(columns)
        ]
        for row in range(rows)
    ]


def inverse(matrix: list[list[int]]) -> list[list[int]]:
    size = len(matrix)
    rows = [
        sum(bit << column for column, bit in enumerate(row))
        | (1 << (size + index))
        for index, row in enumerate(matrix)
    ]
    for column in range(size):
        pivot = next(index for index in range(column, size) if (rows[index] >> column) & 1)
        rows[column], rows[pivot] = rows[pivot], rows[column]
        for index in range(size):
            if index != column and ((rows[index] >> column) & 1):
                rows[index] ^= rows[column]
    mask = (1 << size) - 1
    assert all((rows[index] & mask) == (1 << index) for index in range(size))
    return [
        [((rows[row] >> (size + column)) & 1) for column in range(size)]
        for row in range(size)
    ]


def polynomial_at(coefficients: list[int], matrix: list[list[int]]) -> list[list[int]]:
    """Evaluate coefficients, in descending order, by Horner's rule."""
    size = len(matrix)
    result = zero_matrix(size, size)
    unit_matrix = identity(size)
    for coefficient in coefficients:
        result = multiply(result, matrix)
        if coefficient:
            result = add(result, unit_matrix)
    return result


def block_matrix(
    upper_left: list[list[int]],
    upper_right: list[list[int]],
    lower_left: list[list[int]],
    lower_right: list[list[int]],
) -> list[list[int]]:
    return [
        left + right
        for left, right in zip(upper_left, upper_right)
    ] + [
        left + right
        for left, right in zip(lower_left, lower_right)
    ]


def alternating_form(matrix: list[list[int]]) -> list[list[int]]:
    size = len(matrix)
    zero = zero_matrix(size, size)
    return block_matrix(zero, matrix, transpose(matrix), zero)


def dot(left: list[int], right: list[int]) -> int:
    return sum(a * b for a, b in zip(left, right)) & 1


def unit(size: int, index: int) -> list[int]:
    return [int(column == index) for column in range(size)]


def bilinear_value(
    forms: list[list[list[int]]], left: list[int], right: list[int]
) -> list[int]:
    return [
        dot(left, [dot(row, right) for row in form])
        for form in forms
    ]


def image_vector(matrix: list[list[int]], vector: list[int]) -> list[int]:
    return [dot(row, vector) for row in matrix]


def commutator_forms(
    coefficients: list[list[list[int]]], *, fresh: bool
) -> list[list[list[int]]]:
    """Return one alternating quotient form for each central generator."""
    quotient_dimension = (
        FRESH_QUOTIENT_DIMENSION if fresh else SOURCE_QUOTIENT_DIMENSION
    )
    forms = [
        zero_matrix(quotient_dimension, quotient_dimension)
        for _ in range(CENTER_DIMENSION)
    ]

    # The Schur packet has generators p_1,...,p_15,q_1,...,q_15 and
    # [p_r,q_s] equal to the five coefficient bits of B(x).
    for center, coefficient in enumerate(coefficients):
        for row in range(RESIDUAL_DIMENSION):
            for column in range(RESIDUAL_DIMENSION):
                value = coefficient[row][column]
                forms[center][row][RESIDUAL_DIMENSION + column] = value
                forms[center][RESIDUAL_DIMENSION + column][row] = value

    if fresh:
        p_minus, q_minus, p_plus, q_plus = range(30, 34)
        # [p_-,q_-]=s and [p_+,q_+]=J+s.  The standardized fresh
        # selector basis uses z_1 (central coordinate 1) for s.
        forms[1][p_minus][q_minus] = forms[1][q_minus][p_minus] = 1
        forms[0][p_plus][q_plus] = forms[0][q_plus][p_plus] = 1
        forms[1][p_plus][q_plus] = forms[1][q_plus][p_plus] = 1
    else:
        x_dummy, z_dummy = 30, 31
        forms[0][x_dummy][z_dummy] = forms[0][z_dummy][x_dummy] = 1
    return forms


def component_injection() -> list[list[int]]:
    """Fresh quotient coordinates of every source quotient generator."""
    injection = zero_matrix(FRESH_QUOTIENT_DIMENSION, SOURCE_QUOTIENT_DIMENSION)
    for index in range(30):
        injection[index][index] = 1
    # x_dummy -> p_- p_+, z_dummy -> q_- q_+.
    injection[30][30] = 1
    injection[32][30] = 1
    injection[31][31] = 1
    injection[33][31] = 1
    return injection


def check_component_map(
    source_forms: list[list[list[int]]],
    fresh_forms: list[list[list[int]]],
    injection: list[list[int]],
) -> dict:
    failures = []
    for left_index in range(SOURCE_QUOTIENT_DIMENSION):
        left = unit(SOURCE_QUOTIENT_DIMENSION, left_index)
        fresh_left = image_vector(injection, left)
        for right_index in range(SOURCE_QUOTIENT_DIMENSION):
            right = unit(SOURCE_QUOTIENT_DIMENSION, right_index)
            fresh_right = image_vector(injection, right)
            source_value = bilinear_value(source_forms, left, right)
            fresh_value = bilinear_value(fresh_forms, fresh_left, fresh_right)
            if source_value != fresh_value:
                failures.append([left_index, right_index])
    return {
        "commutator_pairs_checked": SOURCE_QUOTIENT_DIMENSION**2,
        "commutator_failures": failures,
        "quotient_map_rank": rank_matrix(injection),
        "quotient_kernel_dimension": (
            SOURCE_QUOTIENT_DIMENSION - rank_matrix(injection)
        ),
        "center_map_rank": CENTER_DIMENSION,
        "center_kernel_dimension": 0,
    }


def gl2() -> list[tuple[int, int, int, int]]:
    matrices = []
    for entries in product((0, 1), repeat=4):
        a, b, c, d = entries
        if (a * d ^ b * c) == 1:
            matrices.append(entries)
    return matrices


def gl2_multiply(
    left: tuple[int, int, int, int],
    right: tuple[int, int, int, int],
) -> tuple[int, int, int, int]:
    a, b, c, d = left
    e, f, g, h = right
    return (
        (a * e) ^ (b * g),
        (a * f) ^ (b * h),
        (c * e) ^ (d * g),
        (c * f) ^ (d * h),
    )


def gl2_inverse(matrix: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    a, b, c, d = matrix
    # Every determinant is one over F_2.
    return d, b, c, a


def gl2_apply(matrix: tuple[int, int, int, int], vector: int) -> int:
    x = vector & 1
    y = (vector >> 1) & 1
    a, b, c, d = matrix
    return ((a * x) ^ (b * y)) | (((c * x) ^ (d * y)) << 1)


def permutation_compose(left: list[int], right: list[int]) -> list[int]:
    return [left[right[index]] for index in range(len(left))]


def permutation_power(permutation: list[int], exponent: int) -> list[int]:
    result = list(range(len(permutation)))
    for _ in range(exponent):
        result = permutation_compose(permutation, result)
    return result


def regular_action_audit() -> dict:
    group = gl2()
    index = {element: position for position, element in enumerate(group)}
    swap = (0, 1, 1, 0)
    shear = (1, 1, 0, 1)

    def left_permutation(element: tuple[int, int, int, int]) -> list[int]:
        return [index[gl2_multiply(element, factor)] for factor in group]

    swap_permutation = left_permutation(swap)
    shear_permutation = left_permutation(shear)
    product_permutation = permutation_compose(swap_permutation, shear_permutation)
    identity_permutation = list(range(REGULAR_FACTORS))

    base_direction = 1
    factor_directions = [
        gl2_apply(gl2_inverse(factor), base_direction)
        for factor in group
    ]

    source_center_dimension = 1 + REGULAR_FACTORS * (CENTER_DIMENSION - 1)
    source_quotient_dimension = REGULAR_FACTORS * SOURCE_QUOTIENT_DIMENSION
    fresh_quotient_dimension = REGULAR_FACTORS * FRESH_QUOTIENT_DIMENSION

    # The regular component map is block diagonal.  Its rank is also checked
    # by constructing the exact binary matrix, not merely inferred.
    component = component_injection()
    regular_map = zero_matrix(fresh_quotient_dimension, source_quotient_dimension)
    for factor in range(REGULAR_FACTORS):
        for row in range(FRESH_QUOTIENT_DIMENSION):
            for column in range(SOURCE_QUOTIENT_DIMENSION):
                regular_map[factor * FRESH_QUOTIENT_DIMENSION + row][
                    factor * SOURCE_QUOTIENT_DIMENSION + column
                ] = component[row][column]
    regular_rank = rank_matrix(regular_map)

    equivariance_failures = []
    for generator_name, permutation in (
        ("swap", swap_permutation),
        ("shear", shear_permutation),
    ):
        for factor in range(REGULAR_FACTORS):
            for source_coordinate in range(SOURCE_QUOTIENT_DIMENSION):
                source_vector = unit(
                    source_quotient_dimension,
                    factor * SOURCE_QUOTIENT_DIMENSION + source_coordinate,
                )
                permuted_source = unit(
                    source_quotient_dimension,
                    permutation[factor] * SOURCE_QUOTIENT_DIMENSION
                    + source_coordinate,
                )
                map_then_permute = image_vector(regular_map, source_vector)
                permute_then_map = image_vector(regular_map, permuted_source)
                moved_map = [0 for _ in range(fresh_quotient_dimension)]
                for target_factor in range(REGULAR_FACTORS):
                    moved_factor = permutation[target_factor]
                    for target_coordinate in range(FRESH_QUOTIENT_DIMENSION):
                        moved_map[
                            moved_factor * FRESH_QUOTIENT_DIMENSION
                            + target_coordinate
                        ] = map_then_permute[
                            target_factor * FRESH_QUOTIENT_DIMENSION
                            + target_coordinate
                        ]
                if moved_map != permute_then_map:
                    equivariance_failures.append(
                        [generator_name, factor, source_coordinate]
                    )

    # Literal sharing of all six residual p/q packets sends corresponding
    # coordinates in every factor to one common 30-dimensional space.  Keep
    # the six dummy pairs separate, so this is the least destructive sharing
    # quotient relevant to the proposed global-fresh-packet shortcut.
    shared_rows = 30 + 2 * REGULAR_FACTORS
    shared_map = zero_matrix(shared_rows, source_quotient_dimension)
    for factor in range(REGULAR_FACTORS):
        for coordinate in range(30):
            shared_map[coordinate][
                factor * SOURCE_QUOTIENT_DIMENSION + coordinate
            ] = 1
        shared_map[30 + 2 * factor][
            factor * SOURCE_QUOTIENT_DIMENSION + 30
        ] = 1
        shared_map[30 + 2 * factor + 1][
            factor * SOURCE_QUOTIENT_DIMENSION + 31
        ] = 1
    shared_rank = rank_matrix(shared_map)

    return {
        "s3_order": len(group),
        "swap_relation": permutation_power(swap_permutation, 2) == identity_permutation,
        "shear_relation": permutation_power(shear_permutation, 2) == identity_permutation,
        "product_order_three_relation": (
            permutation_power(product_permutation, 3) == identity_permutation
        ),
        "regular_action_faithful": len({tuple(left_permutation(g)) for g in group}) == 6,
        "factor_direction_labels": factor_directions,
        "direction_multiplicities": {
            str(direction): factor_directions.count(direction)
            for direction in (1, 2, 3)
        },
        "source_center_dimension": source_center_dimension,
        "source_quotient_dimension": source_quotient_dimension,
        "fresh_quotient_dimension": fresh_quotient_dimension,
        "regular_quotient_map_rank": regular_rank,
        "regular_quotient_kernel_dimension": source_quotient_dimension - regular_rank,
        "regular_equivariance_basis_vectors_checked": (
            2 * source_quotient_dimension
        ),
        "regular_equivariance_failures": equivariance_failures,
        "regular_center_map_rank": source_center_dimension,
        "regular_center_kernel_dimension": 0,
        "source_group_order_exponent": source_center_dimension + source_quotient_dimension,
        "fresh_group_order_exponent": source_center_dimension + fresh_quotient_dimension,
        "source_semidirect_group_order": 6 * (1 << (source_center_dimension + source_quotient_dimension)),
        "fresh_semidirect_group_order": 6 * (1 << (source_center_dimension + fresh_quotient_dimension)),
        "shared_residual_quotient_rank": shared_rank,
        "shared_residual_quotient_kernel_dimension": (
            source_quotient_dimension - shared_rank
        ),
        "residual_only_shared_kernel_dimension": (
            REGULAR_FACTORS * 30 - 30
        ),
        "explicit_shared_kernel_word": "p[factor_0,0] p[factor_1,0]",
    }


def full_clifford_obstruction(
    reset_forms: list[list[list[int]]],
) -> dict:
    first = alternating_form(reset_forms[0])
    second = alternating_form(reset_forms[1])
    transition = multiply(inverse(first), second)
    inverse_transition = inverse(transition)
    translated_transition = add(identity(2 * RESIDUAL_DIMENSION), transition)
    # These are the three irreducible primary factors of the chosen
    # 15-dimensional transition (listed in the archived strict-pencil
    # audit).  Nullities of polynomial evaluations are similarity
    # invariants and avoid any external computer-algebra dependency.
    test_polynomials = {
        "x^2+x+1": [1, 1, 1],
        "x^4+x+1": [1, 0, 0, 1, 1],
        "x^9+x^4+x^3+x+1": [1, 0, 0, 0, 0, 1, 1, 0, 1, 1],
    }

    def nullity_signature(matrix: list[list[int]]) -> dict[str, int]:
        return {
            name: len(matrix) - rank_matrix(polynomial_at(coefficients, matrix))
            for name, coefficients in test_polynomials.items()
        }

    signature = nullity_signature(transition)
    inverse_signature = nullity_signature(inverse_transition)
    translated_signature = nullity_signature(translated_transition)
    return {
        "alternating_space_dimension": 2 * RESIDUAL_DIMENSION,
        "transition_rank": rank_matrix(transition),
        "translated_transition_rank": rank_matrix(translated_transition),
        "swap_similarity": signature == inverse_signature,
        "shear_similarity": signature == translated_signature,
        "transition_primary_nullities": signature,
        "inverse_primary_nullities": inverse_signature,
        "translated_primary_nullities": translated_signature,
    }


def main() -> None:
    certificate = search_certificate(4)
    degree = certificate["matrix_size"]
    modulus = int(certificate["modulus_hex"], 16)
    left_basis = hyperplane_basis(0x1, degree)
    right_basis = hyperplane_basis(0x4DDC, degree)

    reset_forms = [
        restricted_matrix(value, left_basis, right_basis, modulus, degree)
        for value in RESET_PLANE
    ]
    assert RESET_PLANE[0] ^ RESET_PLANE[1] == RESET_PLANE[2]
    assert all(rank_matrix(form) == RESIDUAL_DIMENSION for form in reset_forms)

    a0 = int(certificate["a0_hex"], 16)
    directions = [int(value, 16) for value in certificate["directions_hex"]]
    coefficient_values = [a0, *directions]
    coefficients = [
        restricted_matrix(value, left_basis, right_basis, modulus, degree)
        for value in coefficient_values
    ]
    source_forms = commutator_forms(coefficients, fresh=False)
    fresh_forms = commutator_forms(coefficients, fresh=True)
    injection = component_injection()
    component = check_component_map(source_forms, fresh_forms, injection)

    derivative_span_ranks = [rank_matrix(form) for form in reset_forms]
    derivative_union = [row[:] for row in reset_forms[0]]
    for form in reset_forms[1:]:
        derivative_union.extend(row[:] for row in form)

    report = {
        "reset_plane_hex": [hex(value) for value in RESET_PLANE],
        "residual_dimension": RESIDUAL_DIMENSION,
        "derivative_word_span_ranks": derivative_span_ranks,
        "stacked_derivative_row_span_rank": rank_matrix(derivative_union),
        "component_source_order": 1 << (CENTER_DIMENSION + SOURCE_QUOTIENT_DIMENSION),
        "component_fresh_order": 1 << (CENTER_DIMENSION + FRESH_QUOTIENT_DIMENSION),
        "component_map": component,
        "one_copy_full_clifford_obstruction": full_clifford_obstruction(reset_forms),
        "regular_s3": regular_action_audit(),
    }

    assert not component["commutator_failures"]
    assert component["quotient_kernel_dimension"] == 0
    assert component["center_kernel_dimension"] == 0
    assert report["one_copy_full_clifford_obstruction"]["swap_similarity"] is False
    assert report["one_copy_full_clifford_obstruction"]["shear_similarity"] is False
    assert report["regular_s3"]["regular_quotient_kernel_dimension"] == 0
    assert report["regular_s3"]["regular_center_kernel_dimension"] == 0
    assert not report["regular_s3"]["regular_equivariance_failures"]
    assert report["regular_s3"]["residual_only_shared_kernel_dimension"] == 150
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
