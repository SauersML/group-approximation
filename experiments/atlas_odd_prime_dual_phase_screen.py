"""Search odd-characteristic permutation modules for an atlas phase seed.

For the A8 actions on the 15 points and 15 hyperplanes of F2^4, linearize
the inner-aligned two-chart atlas over F_p[eps]/(eps^2).  The 24 certified
zero derivatives must vanish and all four survivor derivatives must
intertwine the first chart.  Exact modular row reduction tests whether the
marked survivor s_11 can remain nonzero and extracts a tangent when it can.
"""

import argparse
import json

import numpy as np

from atlas_certified_a8_alignment import (
    CERTIFIED_REPRESENTATIVE_INDICES,
    PHASE_INDEX,
    boundary_words,
)
from atlas_certified_dual_number_certificate import ALIGNMENT_KEY
from atlas_subset_dual_central_no_go import SURVIVOR_REPRESENTATIVES
from atlas_two_chart_search import (
    factor_generators,
    gf2_inv,
    gf2_mul,
    matrix_key,
)


NONZERO_VECTORS = tuple(
    np.asarray([(value >> index) & 1 for index in range(4)], dtype=np.uint8)
    for value in range(1, 16)
)
NONZERO_VECTOR_LOOKUP = {
    tuple(int(entry) for entry in vector): index
    for index, vector in enumerate(NONZERO_VECTORS)
}


def point_permutation(matrix):
    result = np.zeros((15, 15), dtype=np.int64)
    for source, vector in enumerate(NONZERO_VECTORS):
        target_vector = gf2_mul(matrix, vector.reshape(4, 1)).reshape(4)
        target = NONZERO_VECTOR_LOOKUP[
            tuple(int(entry) for entry in target_vector)
        ]
        result[target, source] = 1
    return result


def hyperplane_permutation(matrix):
    return point_permutation(gf2_inv(matrix).T.copy())


MODULES = (
    ("point_permutation_15", point_permutation),
    ("hyperplane_permutation_15", hyperplane_permutation),
)


def inverse_mod_prime(matrix, prime):
    dimension = matrix.shape[0]
    augmented = np.concatenate((
        matrix.copy() % prime,
        np.eye(dimension, dtype=np.int64),
    ), axis=1)
    for column in range(dimension):
        pivots = np.flatnonzero(augmented[column:, column] % prime)
        if len(pivots) == 0:
            raise ValueError("singular matrix modulo prime")
        pivot = column + int(pivots[0])
        if pivot != column:
            augmented[[column, pivot]] = augmented[[pivot, column]]
        inverse = pow(int(augmented[column, column]), prime - 2, prime)
        augmented[column] = (augmented[column] * inverse) % prime
        for row in range(dimension):
            if row != column and augmented[row, column]:
                factor = int(augmented[row, column])
                augmented[row] = (
                    augmented[row] - factor * augmented[column]
                ) % prime
    return augmented[:, dimension:]


def module_record(name, representation, source_elements, prime):
    represented = {
        matrix_key(matrix).hex(): representation(matrix) % prime
        for matrix in source_elements
    }
    alignment_source = np.frombuffer(
        bytes.fromhex(ALIGNMENT_KEY), dtype=np.uint8
    ).reshape(4, 4)
    alignment = representation(alignment_source) % prime
    return {
        "name": name,
        "dimension": alignment.shape[0],
        "represented": represented,
        "alignment": alignment,
        "alignment_inverse": inverse_mod_prime(alignment, prime),
    }


def derivative_operator(word, left_module, right_module, prime):
    left_dimension = left_module["dimension"]
    right_dimension = right_module["dimension"]
    left_prefix = np.eye(left_dimension, dtype=np.int64)
    right_prefix = np.eye(right_dimension, dtype=np.int64)
    operator = np.zeros((
        left_dimension * right_dimension,
        left_dimension * right_dimension,
    ), dtype=np.int64)

    for factor, source_matrix in word:
        key = matrix_key(source_matrix).hex()
        left = left_module["represented"][key]
        right = right_module["represented"][key]
        if factor == 2:
            left = (
                left_module["alignment"] @ left
                @ left_module["alignment_inverse"]
            ) % prime
            right = (
                right_module["alignment"] @ right
                @ right_module["alignment_inverse"]
            ) % prime
        left_before = left_prefix
        right_before = right_prefix
        left_prefix = (left_prefix @ left) % prime
        right_prefix = (right_prefix @ right) % prime
        if factor == 2:
            operator += np.kron(
                left_before,
                inverse_mod_prime(right_before, prime).T,
            )
            operator -= np.kron(
                left_prefix,
                inverse_mod_prime(right_prefix, prime).T,
            )
            operator %= prime

    if not np.array_equal(
            left_prefix % prime,
            np.eye(left_dimension, dtype=np.int64)):
        raise AssertionError("left aligned base word is not identity")
    if not np.array_equal(
            right_prefix % prime,
            np.eye(right_dimension, dtype=np.int64)):
        raise AssertionError("right aligned base word is not identity")
    return operator % prime


def centrality_operator(left_generator, right_generator, prime):
    left_dimension = left_generator.shape[0]
    right_dimension = right_generator.shape[0]
    return (
        np.kron(np.eye(left_dimension, dtype=np.int64), right_generator.T)
        - np.kron(left_generator, np.eye(right_dimension, dtype=np.int64))
    ) % prime


def insert_modular_row(basis, raw_row, prime):
    row = np.asarray(raw_row, dtype=np.int64).copy() % prime
    while True:
        nonzero = np.flatnonzero(row)
        if len(nonzero) == 0:
            return False
        pivot = int(nonzero[-1])
        other = basis.get(pivot)
        if other is None:
            inverse = pow(int(row[pivot]), prime - 2, prime)
            basis[pivot] = (row * inverse) % prime
            return True
        row = (row - int(row[pivot]) * other) % prime


def reduce_modular_row(basis, raw_row, prime):
    row = np.asarray(raw_row, dtype=np.int64).copy() % prime
    while True:
        nonzero = np.flatnonzero(row)
        if len(nonzero) == 0:
            return row
        pivot = int(nonzero[-1])
        other = basis.get(pivot)
        if other is None:
            return row
        row = (row - int(row[pivot]) * other) % prime


def solve_affine(equations, width, prime):
    basis = {}
    for raw_row, raw_right in equations:
        row = np.asarray(raw_row, dtype=np.int64).copy() % prime
        right = int(raw_right) % prime
        while True:
            nonzero = np.flatnonzero(row)
            if len(nonzero) == 0:
                if right:
                    return None
                break
            pivot = int(nonzero[-1])
            entry = basis.get(pivot)
            if entry is None:
                inverse = pow(int(row[pivot]), prime - 2, prime)
                basis[pivot] = (
                    (row * inverse) % prime,
                    right * inverse % prime,
                )
                break
            other, other_right = entry
            factor = int(row[pivot])
            row = (row - factor * other) % prime
            right = (right - factor * other_right) % prime

    solution = np.zeros(width, dtype=np.int64)
    for pivot in sorted(basis):
        row, right = basis[pivot]
        known = int(np.dot(row[:pivot], solution[:pivot]) % prime)
        solution[pivot] = (right - known) % prime
    for row, right in equations:
        if int(np.dot(row, solution) % prime) != int(right) % prime:
            raise AssertionError("modular affine solve returned false witness")
    return solution


def analyze_block(left, right, words, source_generators, prime):
    selected = sorted(set(
        CERTIFIED_REPRESENTATIVE_INDICES + SURVIVOR_REPRESENTATIVES
    ))
    derivatives = {
        index: derivative_operator(words[index], left, right, prime)
        for index in selected
    }
    generators = [(
        left["represented"][matrix_key(generator).hex()],
        right["represented"][matrix_key(generator).hex()],
    ) for generator in source_generators]

    basis = {}
    for index in CERTIFIED_REPRESENTATIVE_INDICES:
        for row in derivatives[index]:
            insert_modular_row(basis, row, prime)
    for index in SURVIVOR_REPRESENTATIVES:
        derivative = derivatives[index]
        for left_generator, right_generator in generators:
            constraints = centrality_operator(
                left_generator, right_generator, prime
            ) @ derivative % prime
            for row in constraints:
                insert_modular_row(basis, row, prime)

    rank = len(basis)
    phase_rows = derivatives[PHASE_INDEX]
    surviving_outputs = [
        output for output, row in enumerate(phase_rows)
        if np.any(reduce_modular_row(basis, row, prime))
    ]
    combined = dict(basis)
    for row in phase_rows:
        insert_modular_row(combined, row, prime)

    witness = None
    if surviving_outputs:
        output = surviving_outputs[0]
        equations = [(row, 0) for row in basis.values()]
        equations.append((phase_rows[output], 1))
        solution = solve_affine(
            equations, phase_rows.shape[1], prime
        )
        if solution is None:
            raise AssertionError("rank increase had no affine witness")
        witness = {
            "forced_phase_output": divmod(output, right["dimension"]),
            "tangent_support": [
                [index // right["dimension"], index % right["dimension"],
                 int(value)]
                for index, value in enumerate(solution) if value
            ],
            "tangent_support_size": int(np.count_nonzero(solution)),
        }

    width = left["dimension"] * right["dimension"]
    return {
        "prime": prime,
        "left_module": left["name"],
        "right_module": right["name"],
        "hom_dimension": width,
        "constraint_rank": rank,
        "constraint_nullity": width - rank,
        "phase_image_dimension": len(combined) - rank,
        "nonzero_central_phase_exists": bool(surviving_outputs),
        "witness": witness,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--primes", default="3,5,7,11",
        help="comma-separated odd primes",
    )
    args = parser.parse_args()
    primes = [int(value) for value in args.primes.split(",")]

    words = boundary_words()
    source_elements = {}
    for word in words:
        for _factor, matrix in word:
            source_elements[matrix_key(matrix).hex()] = matrix
    source_generators = [
        word[0][1] for _name, word in factor_generators()[:6]
    ]
    records = []
    for prime in primes:
        modules = [
            module_record(
                name, representation, source_elements.values(), prime
            )
            for name, representation in MODULES
        ]
        for left in modules:
            for right in modules:
                records.append(analyze_block(
                    left, right, words, source_generators, prime
                ))

    print(json.dumps({
        "coefficient_rings": [
            "F_%d[eps]/(eps^2)" % prime for prime in primes
        ],
        "modules": [name for name, _representation in MODULES],
        "centrality_condition":
            "every survivor block intertwines the first A8 chart",
        "ordered_block_records": records,
        "some_nonzero_central_phase_exists": any(
            record["nonzero_central_phase_exists"] for record in records
        ),
    }, indent=2))


if __name__ == "__main__":
    main()
