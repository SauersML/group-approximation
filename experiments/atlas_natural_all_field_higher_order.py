"""Certify all-order atlas rigidity in the natural A8 module over all fields.

The universal first-order theorem kills the marked phase but leaves two
noncommutant tangent directions in the natural eight-point permutation
module in good odd characteristic.  Work over F_p[eps]/(eps^3), quotient
the tangent kernel by the two-dimensional chart commutant, exhaust its
projective lines, and solve the exact affine equations for the second jet.

An exact integral rank minor has determinant 2^13, so in every odd
characteristic the constrained tangent kernel is exactly the two-dimensional
chart commutant.  The characteristic-two noncommutant line is independently
replayed and shown quadratically obstructed.  These facts give the all-order
formal conclusion recorded in the companion theorem note.
"""

import argparse
import json

import numpy as np

from atlas_certified_a8_alignment import (
    CERTIFIED_REPRESENTATIVE_INDICES,
    PHASE_INDEX,
    boundary_words,
)
from atlas_certified_dual_number_certificate import (
    ALIGNMENT_KEY,
    natural_a8_map,
    permutation_matrix,
)
from atlas_subset_dual_central_no_go import SURVIVOR_REPRESENTATIVES
from atlas_subset_dual_commutant_phase import subset_module
from atlas_two_chart_search import factor_generators, matrix_key


def multiply(left, right, prime):
    return (left @ right) % prime


def triple_multiply(left, right, prime):
    a0, a1, a2 = left
    b0, b1, b2 = right
    return (
        multiply(a0, b0, prime),
        (multiply(a0, b1, prime) + multiply(a1, b0, prime)) % prime,
        (
            multiply(a0, b2, prime)
            + multiply(a1, b1, prime)
            + multiply(a2, b0, prime)
        ) % prime,
    )


def chart_triples(module, tangent, second_tangent, prime):
    dimension = module["dimension"]
    identity = np.eye(dimension, dtype=np.int64)
    zero = np.zeros((dimension, dimension), dtype=np.int64)
    alignment = permutation_matrix(module["alignment"]).astype(np.int64)
    alignment_inverse = alignment.T.copy()
    tangent_square = multiply(tangent, tangent, prime)
    relative = (
        alignment,
        multiply(tangent, alignment, prime),
        multiply(second_tangent, alignment, prime),
    )
    relative_inverse = (
        alignment_inverse,
        (-multiply(alignment_inverse, tangent, prime)) % prime,
        multiply(
            alignment_inverse,
            (tangent_square - second_tangent) % prime,
            prime,
        ),
    )
    first = {}
    second = {}
    for key, permutation in module["represented"].items():
        value = permutation_matrix(permutation).astype(np.int64)
        first[key] = (value, zero, zero)
        second[key] = triple_multiply(
            triple_multiply(relative, (value, zero, zero), prime),
            relative_inverse,
            prime,
        )
    return first, second, identity, zero


def evaluate(word, first, second, identity, zero, prime):
    value = (identity, zero, zero)
    for factor, source_matrix in word:
        chart = first if factor == 1 else second
        value = triple_multiply(
            value, chart[matrix_key(source_matrix).hex()], prime
        )
    return value


def row_reduce(input_matrix, prime):
    reduced = input_matrix.copy() % prime
    row_count, column_count = reduced.shape
    pivot_columns = []
    pivot_row = 0
    for column in range(column_count):
        candidates = np.flatnonzero(reduced[pivot_row:, column])
        if not len(candidates):
            continue
        source_row = pivot_row + int(candidates[0])
        if source_row != pivot_row:
            reduced[[pivot_row, source_row]] = reduced[
                [source_row, pivot_row]
            ]
        inverse = pow(int(reduced[pivot_row, column]), prime - 2, prime)
        reduced[pivot_row] = reduced[pivot_row] * inverse % prime
        factors = reduced[:, column].copy()
        factors[pivot_row] = 0
        nonzero_rows = np.flatnonzero(factors)
        if len(nonzero_rows):
            reduced[nonzero_rows] = (
                reduced[nonzero_rows]
                - factors[nonzero_rows, None] * reduced[pivot_row]
            ) % prime
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == row_count:
            break
    return reduced, pivot_columns


def nullspace(input_matrix, prime):
    reduced, pivots = row_reduce(input_matrix, prime)
    free_columns = [
        column for column in range(input_matrix.shape[1])
        if column not in set(pivots)
    ]
    vectors = []
    for free_column in free_columns:
        vector = np.zeros(input_matrix.shape[1], dtype=np.int64)
        vector[free_column] = 1
        for row, pivot in enumerate(pivots):
            vector[pivot] = -reduced[row, free_column] % prime
        if np.any(input_matrix @ vector % prime):
            raise AssertionError("nullspace reconstruction failed")
        vectors.append(vector)
    return vectors


def rank(vectors, width, prime):
    if not vectors:
        return 0
    return len(row_reduce(np.vstack(vectors).reshape(-1, width), prime)[1])


def prepare_affine_solver(matrix, prime):
    """Row-reduce once and retain the operations acting on right sides."""
    reduced = matrix.copy() % prime
    row_count, column_count = reduced.shape
    pivot_columns = []
    operations = []
    pivot_row = 0
    for column in range(column_count):
        candidates = np.flatnonzero(reduced[pivot_row:, column])
        if not len(candidates):
            continue
        source_row = pivot_row + int(candidates[0])
        if source_row != pivot_row:
            reduced[[pivot_row, source_row]] = reduced[
                [source_row, pivot_row]
            ]
        inverse = pow(int(reduced[pivot_row, column]), prime - 2, prime)
        reduced[pivot_row] = reduced[pivot_row] * inverse % prime
        factors = reduced[:, column].copy()
        factors[pivot_row] = 0
        affected = np.flatnonzero(factors)
        affected_factors = factors[affected].copy()
        if len(affected):
            reduced[affected] = (
                reduced[affected]
                - affected_factors[:, None] * reduced[pivot_row]
            ) % prime
        operations.append((
            pivot_row, source_row, inverse,
            affected, affected_factors,
        ))
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == row_count:
            break
    if np.any(reduced[pivot_row:]):
        raise AssertionError("affine coefficient reduction is incomplete")
    return {
        "matrix": matrix,
        "prime": prime,
        "rank": pivot_row,
        "pivot_columns": pivot_columns,
        "operations": operations,
    }


def solve_prepared(solver, right_side):
    prime = solver["prime"]
    transformed = right_side.copy() % prime
    for (
        pivot_row, source_row, inverse,
        affected, affected_factors,
    ) in solver["operations"]:
        if source_row != pivot_row:
            transformed[pivot_row], transformed[source_row] = (
                transformed[source_row], transformed[pivot_row]
            )
        transformed[pivot_row] = transformed[pivot_row] * inverse % prime
        if len(affected):
            transformed[affected] = (
                transformed[affected]
                - affected_factors * transformed[pivot_row]
            ) % prime
    if np.any(transformed[solver["rank"]:]):
        return None
    solution = np.zeros(solver["matrix"].shape[1], dtype=np.int64)
    for row, pivot in enumerate(solver["pivot_columns"]):
        solution[pivot] = transformed[row]
    if np.any(
        (solver["matrix"] @ solution - right_side) % prime
    ):
        raise AssertionError("affine solver returned a false witness")
    return solution


def commutator(matrix, generator, prime):
    return (
        multiply(matrix, generator, prime)
        - multiply(generator, matrix, prime)
    ) % prime


def flatten(matrix):
    return matrix.reshape(-1)


def matrix_from_vector(vector, dimension):
    return vector.reshape(dimension, dimension)


def constraint_vector(values, generators, prime):
    pieces = [
        flatten(values[index])
        for index in CERTIFIED_REPRESENTATIVE_INDICES
    ]
    for index in SURVIVOR_REPRESENTATIVES:
        for generator in generators:
            pieces.append(flatten(commutator(
                values[index], generator, prime
            )))
    return np.concatenate(pieces) % prime


def word_derivative_operator(word, module):
    dimension = module["dimension"]
    identity = np.eye(dimension, dtype=np.int64)
    alignment = permutation_matrix(module["alignment"]).astype(np.int64)
    alignment_inverse = alignment.T.copy()
    prefix = identity
    result = np.zeros(
        (dimension * dimension, dimension * dimension), dtype=np.int64
    )
    for factor, source_matrix in word:
        image = permutation_matrix(module["represented"][
            matrix_key(source_matrix).hex()
        ]).astype(np.int64)
        if factor == 2:
            image = alignment @ image @ alignment_inverse
        before = prefix
        prefix = prefix @ image
        if factor == 2:
            result += np.kron(before, before)
            result -= np.kron(prefix, prefix)
    if np.any(prefix - identity):
        raise AssertionError("aligned word is nontrivial at order zero")
    return result


def build_linear_system(module, words, generators):
    dimension = module["dimension"]
    width = dimension * dimension
    selected = sorted(set(
        CERTIFIED_REPRESENTATIVE_INDICES + SURVIVOR_REPRESENTATIVES
    ))
    derivatives = {
        index: word_derivative_operator(words[index], module)
        for index in selected
    }
    blocks = [
        derivatives[index]
        for index in CERTIFIED_REPRESENTATIVE_INDICES
    ]
    identity = np.eye(dimension, dtype=np.int64)
    for index in SURVIVOR_REPRESENTATIVES:
        for generator in generators:
            commutator_operator = (
                np.kron(identity, generator.T)
                - np.kron(generator, identity)
            )
            blocks.append(commutator_operator @ derivatives[index])

    # One direct truncated-ring evaluation guards the vectorization and
    # alignment conventions used by the much faster prefix formula.
    return np.vstack(blocks), derivatives[PHASE_INDEX]


def chart_commutant_system(dimension, generators, prime):
    width = dimension * dimension
    columns = []
    for variable in range(width):
        matrix = np.zeros((dimension, dimension), dtype=np.int64)
        matrix.reshape(-1)[variable] = 1
        columns.append(np.concatenate([
            flatten(commutator(matrix, generator, prime))
            for generator in generators
        ]))
    return np.column_stack(columns) % prime


def quotient_complement(kernel, commutant, width, prime):
    span = list(commutant)
    current_rank = rank(span, width, prime)
    complement = []
    for vector in kernel:
        candidate_rank = rank(span + [vector], width, prime)
        if candidate_rank > current_rank:
            span.append(vector)
            complement.append(vector)
            current_rank = candidate_rank
    return complement


def projective_representatives(basis, prime, width):
    if not basis:
        yield np.zeros(width, dtype=np.int64)
        return
    yield np.zeros_like(basis[0])
    dimension = len(basis)
    for leading in range(dimension):
        suffix_dimension = dimension - leading - 1
        for encoded in range(prime ** suffix_dimension):
            coefficients = [0] * leading + [1]
            for _index in range(suffix_dimension):
                coefficients.append(encoded % prime)
                encoded //= prime
            vector = np.zeros_like(basis[0])
            for coefficient, basis_vector in zip(coefficients, basis):
                vector = (vector + coefficient * basis_vector) % prime
            yield vector


def analyze_prime(
        prime, max_tangents, module, words,
        generators, integer_equations, integer_phase_linear):
    dimension = module["dimension"]
    width = dimension * dimension
    equations = integer_equations % prime
    phase_linear = integer_phase_linear % prime
    affine_solver = prepare_affine_solver(equations, prime)
    kernel = nullspace(equations, prime)
    commutant = nullspace(
        chart_commutant_system(dimension, generators, prime), prime
    )
    complement = quotient_complement(kernel, commutant, width, prime)
    if len(kernel) - len(commutant) != len(complement):
        raise AssertionError("tangent quotient decomposition failed")

    zero = np.zeros((dimension, dimension), dtype=np.int64)
    selected = sorted(set(
        CERTIFIED_REPRESENTATIVE_INDICES + SURVIVOR_REPRESENTATIVES
    ))
    records = []
    representatives_total = 1 + sum(
        prime ** exponent for exponent in range(len(complement))
    )
    tested_all = max_tangents is None or representatives_total <= max_tangents
    for representative_index, tangent_vector in enumerate(
            projective_representatives(complement, prime, width)):
        if max_tangents is not None and representative_index >= max_tangents:
            break
        tangent = matrix_from_vector(tangent_vector, dimension)
        first, second, identity, triple_zero = chart_triples(
            module, tangent, zero, prime
        )
        quadratic = {
            index: evaluate(
                words[index], first, second, identity, triple_zero, prime
            )[2]
            for index in selected
        }
        right_side = -constraint_vector(
            quadratic, generators, prime
        ) % prime
        second_vector = solve_prepared(affine_solver, right_side)
        if second_vector is None:
            records.append({
                "projective_representative": representative_index,
                "tangent_weight": int(np.count_nonzero(tangent)),
                "second_order_extension_exists": False,
                "second_order_phase_nonzero": False,
            })
            continue
        second_tangent = matrix_from_vector(second_vector, dimension)
        phase = (
            phase_linear @ second_vector
            + flatten(quadratic[PHASE_INDEX])
        ) % prime
        # Replay every equation with the recovered second tangent.
        replay_first, replay_second, replay_identity, replay_zero = (
            chart_triples(module, tangent, second_tangent, prime)
        )
        replay_values = {
            index: evaluate(
                words[index], replay_first, replay_second,
                replay_identity, replay_zero, prime
            )
            for index in selected
        }
        if any(np.any(replay_values[index][1:])
               for index in CERTIFIED_REPRESENTATIVE_INDICES):
            raise AssertionError("zero relation replay failed")
        for index in SURVIVOR_REPRESENTATIVES:
            for generator in generators:
                if np.any(commutator(
                        replay_values[index][1], generator, prime)):
                    raise AssertionError("first-order centrality replay failed")
                if np.any(commutator(
                        replay_values[index][2], generator, prime)):
                    raise AssertionError("second-order centrality replay failed")
        if np.any(phase - flatten(replay_values[PHASE_INDEX][2])):
            raise AssertionError("phase replay failed")
        record = {
            "projective_representative": representative_index,
            "tangent_weight": int(np.count_nonzero(tangent)),
            "second_order_extension_exists": True,
            "second_order_phase_nonzero": bool(np.any(phase)),
            "second_order_phase_weight": int(np.count_nonzero(phase)),
        }
        if np.any(tangent) or np.any(phase):
            record.update({
                "tangent": tangent.tolist(),
                "second_tangent": second_tangent.tolist(),
                "phase": matrix_from_vector(phase, dimension).tolist(),
            })
        records.append(record)

    return {
        "prime": prime,
        "module": "natural eight-point permutation module",
        "endomorphism_dimension": width,
        "constraint_rank": affine_solver["rank"],
        "constraint_nullity": len(kernel),
        "chart_commutant_dimension": len(commutant),
        "noncommutant_tangent_quotient_dimension": len(complement),
        "projective_tangents_tested_including_zero": len(records),
        "projective_tangents_total_including_zero": representatives_total,
        "projective_tangent_space_exhausted": tested_all,
        "second_order_extensions": sum(
            record["second_order_extension_exists"] for record in records
        ),
        "nonzero_second_order_phases": sum(
            record["second_order_phase_nonzero"] for record in records
        ),
        "records": records,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", default="17,19,23")
    parser.add_argument("--max-tangents", type=int)
    parser.add_argument("--exact-rank-audit", action="store_true")
    args = parser.parse_args()
    images = natural_a8_map()
    words = boundary_words()
    module = subset_module(1, images)
    generators = [
        permutation_matrix(module["represented"][
            matrix_key(word[0][1]).hex()
        ]).astype(np.int64)
        for _name, word in factor_generators()[:6]
    ]
    integer_equations, integer_phase_linear = build_linear_system(
        module, words, generators
    )

    # Guard the integral prefix formula against a direct truncated-ring
    # evaluation before using it in either the rank or quadratic audit.
    dimension = module["dimension"]
    width = dimension * dimension
    test_prime = 17
    test_tangent = np.arange(width, dtype=np.int64).reshape(
        dimension, dimension
    ) % test_prime
    zero = np.zeros((dimension, dimension), dtype=np.int64)
    first, second, triple_identity, triple_zero = chart_triples(
        module, test_tangent, zero, test_prime
    )
    selected = sorted(set(
        CERTIFIED_REPRESENTATIVE_INDICES + SURVIVOR_REPRESENTATIVES
    ))
    derivatives = {
        index: word_derivative_operator(words[index], module)
        for index in selected
    }
    for index in selected:
        direct = evaluate(
            words[index], first, second,
            triple_identity, triple_zero, test_prime,
        )[1]
        predicted = derivatives[index] @ flatten(test_tangent) % test_prime
        if np.any(predicted - flatten(direct)):
            raise AssertionError("prefix derivative convention mismatch")

    exact_rank_audit = None
    if args.exact_rank_audit:
        from sage.all import QQ, ZZ, matrix  # pylint: disable=import-error

        exact_matrix = matrix(ZZ, integer_equations.tolist())
        rational_matrix = exact_matrix.change_ring(QQ)
        column_pivots = list(rational_matrix.echelon_form().pivots())
        row_pivots = list(
            rational_matrix.transpose().echelon_form().pivots()
        )
        rank_over_q = len(column_pivots)
        if len(row_pivots) != rank_over_q:
            raise AssertionError("row/column rank mismatch")
        minor = exact_matrix.matrix_from_rows_and_columns(
            row_pivots, column_pivots
        )
        determinant = ZZ(minor.determinant())
        if not determinant:
            raise AssertionError("selected exact rank minor is singular")
        exact_rank_audit = {
            "rank_over_q": rank_over_q,
            "witness_minor_dimension": rank_over_q,
            "witness_minor_determinant_absolute": str(abs(determinant)),
            "witness_minor_prime_support": [
                [int(prime), int(exponent)]
                for prime, exponent in abs(determinant).factor()
            ],
            "row_indices": row_pivots,
            "column_indices": column_pivots,
        }
    records = [
        analyze_prime(
            int(prime), args.max_tangents, module, words, generators,
            integer_equations, integer_phase_linear,
        )
        for prime in args.primes.split(",")
    ]
    print(json.dumps({
        "coefficient_rings": [
            "F_%d[eps]/(eps^3)" % record["prime"]
            for record in records
        ],
        "records": records,
        "exact_rank_audit": exact_rank_audit,
        "any_nonzero_second_order_phase": any(
            record["nonzero_second_order_phases"]
            for record in records
        ),
    }, indent=2))


if __name__ == "__main__":
    main()
