"""Screen the six repo-native F2[A8]-modules for a central atlas phase.

The modules are the defining and dual four-dimensional GL(4,2)-modules,
their exterior square, the point and hyperplane permutation modules, and the
endomorphism module.  For every ordered Hom block between these modules,
impose the 24 certified-zero derivatives and require all four survivor
derivatives to intertwine the first A8 chart.  Exact F2 row reduction then
tests whether survivor 11 can remain nonzero.
"""

from itertools import combinations
import json

import numpy as np

from atlas_certified_a8_alignment import (
    CERTIFIED_REPRESENTATIVE_INDICES,
    PHASE_INDEX,
    boundary_words,
)
from atlas_certified_dual_number_certificate import ALIGNMENT_KEY
from atlas_subset_dual_central_no_go import (
    SURVIVOR_REPRESENTATIVES,
    insert_row,
    reduce_row,
)
from atlas_subset_dual_commutant_phase import solve_affine
from atlas_two_chart_search import factor_generators, gf2_mul, matrix_key


def gf2_inverse(matrix):
    dimension = matrix.shape[0]
    identity = np.eye(dimension, dtype=np.uint8)
    augmented = np.concatenate((matrix.copy(), identity), axis=1)
    for column in range(dimension):
        pivots = np.flatnonzero(augmented[column:, column])
        if len(pivots) == 0:
            raise ValueError("singular F2 matrix")
        pivot = column + int(pivots[0])
        if pivot != column:
            augmented[[column, pivot]] = augmented[[pivot, column]]
        for row in range(dimension):
            if row != column and augmented[row, column]:
                augmented[row] ^= augmented[column]
    return augmented[:, dimension:]


def natural(matrix):
    return matrix.copy()


def dual(matrix):
    return gf2_inverse(matrix).T.copy()


def exterior_square(matrix):
    pairs = tuple(combinations(range(4), 2))
    result = np.zeros((len(pairs), len(pairs)), dtype=np.uint8)
    for source, (a, b) in enumerate(pairs):
        for target, (i, j) in enumerate(pairs):
            result[target, source] = (
                matrix[i, a] * matrix[j, b]
                ^ matrix[j, a] * matrix[i, b]
            )
    return result


def tensor_natural_dual(matrix):
    return np.kron(matrix, dual(matrix)).astype(np.uint8)


NONZERO_VECTORS = tuple(
    np.array([(value >> index) & 1 for index in range(4)], dtype=np.uint8)
    for value in range(1, 16)
)
NONZERO_VECTOR_LOOKUP = {
    tuple(int(entry) for entry in vector): index
    for index, vector in enumerate(NONZERO_VECTORS)
}


def point_permutation(matrix):
    result = np.zeros((15, 15), dtype=np.uint8)
    for source, vector in enumerate(NONZERO_VECTORS):
        target_vector = gf2_mul(matrix, vector.reshape(4, 1)).reshape(4)
        target = NONZERO_VECTOR_LOOKUP[
            tuple(int(entry) for entry in target_vector)
        ]
        result[target, source] = 1
    return result


def hyperplane_permutation(matrix):
    return point_permutation(dual(matrix))


MODULES = (
    ("natural_4", natural),
    ("dual_4", dual),
    ("wedge2_6", exterior_square),
    ("point_permutation_15", point_permutation),
    ("hyperplane_permutation_15", hyperplane_permutation),
    ("natural_tensor_dual_16", tensor_natural_dual),
)


def module_record(name, representation, source_elements):
    represented = {
        matrix_key(matrix).hex(): representation(matrix)
        for matrix in source_elements
    }
    alignment_source = np.frombuffer(
        bytes.fromhex(ALIGNMENT_KEY), dtype=np.uint8
    ).reshape(4, 4)
    alignment = representation(alignment_source)
    return {
        "name": name,
        "dimension": alignment.shape[0],
        "represented": represented,
        "alignment": alignment,
        "alignment_inverse": gf2_inverse(alignment),
    }


def derivative_rows(word, left_module, right_module):
    left_dimension = left_module["dimension"]
    right_dimension = right_module["dimension"]
    left_identity = np.eye(left_dimension, dtype=np.uint8)
    right_identity = np.eye(right_dimension, dtype=np.uint8)
    left_prefix = left_identity
    right_prefix = right_identity
    terms = []
    for factor, source_matrix in word:
        key = matrix_key(source_matrix).hex()
        left = left_module["represented"][key]
        right = right_module["represented"][key]
        if factor == 2:
            left = gf2_mul(gf2_mul(
                left_module["alignment"], left
            ), left_module["alignment_inverse"])
            right = gf2_mul(gf2_mul(
                right_module["alignment"], right
            ), right_module["alignment_inverse"])
        left_before = left_prefix
        right_before = right_prefix
        left_prefix = gf2_mul(left_prefix, left)
        right_prefix = gf2_mul(right_prefix, right)
        if factor == 2:
            terms.extend((
                (left_before, right_before),
                (left_prefix, right_prefix),
            ))
    if not np.array_equal(left_prefix, left_identity):
        raise AssertionError("left base alignment did not kill selected word")
    if not np.array_equal(right_prefix, right_identity):
        raise AssertionError("right base alignment did not kill selected word")

    width = left_dimension * right_dimension
    rows = [0] * width
    for source_index in range(width):
        source_row, source_column = divmod(source_index, right_dimension)
        matrix_unit = np.zeros(
            (left_dimension, right_dimension), dtype=np.uint8
        )
        matrix_unit[source_row, source_column] = 1
        output = np.zeros_like(matrix_unit)
        for left_prefix, right_prefix in terms:
            output ^= gf2_mul(gf2_mul(
                left_prefix, matrix_unit
            ), gf2_inverse(right_prefix))
        for row in range(left_dimension):
            for column in range(right_dimension):
                if output[row, column]:
                    rows[right_dimension * row + column] |= 1 << source_index
    return rows


def intertwiner_rows(
        derivative, left_generator, right_generator,
        left_dimension, right_dimension):
    rows = []
    for row in range(left_dimension):
        for column in range(right_dimension):
            equation = 0
            for middle in range(right_dimension):
                if right_generator[middle, column]:
                    equation ^= derivative[right_dimension * row + middle]
            for middle in range(left_dimension):
                if left_generator[row, middle]:
                    equation ^= derivative[right_dimension * middle + column]
            rows.append(equation)
    return rows


def analyze_block(left_module, right_module, words, source_generators):
    left_dimension = left_module["dimension"]
    right_dimension = right_module["dimension"]
    width = left_dimension * right_dimension
    selected = sorted(set(
        CERTIFIED_REPRESENTATIVE_INDICES + SURVIVOR_REPRESENTATIVES
    ))
    derivatives = {
        index: derivative_rows(words[index], left_module, right_module)
        for index in selected
    }
    generators = [(
        left_module["represented"][matrix_key(generator).hex()],
        right_module["represented"][matrix_key(generator).hex()],
    ) for generator in source_generators]

    basis = {}
    for index in CERTIFIED_REPRESENTATIVE_INDICES:
        for row in derivatives[index]:
            insert_row(basis, row)
    for index in SURVIVOR_REPRESENTATIVES:
        for left_generator, right_generator in generators:
            for row in intertwiner_rows(
                    derivatives[index], left_generator, right_generator,
                    left_dimension, right_dimension):
                insert_row(basis, row)

    phase_remainders = [
        (output_index, reduce_row(basis, row))
        for output_index, row in enumerate(derivatives[PHASE_INDEX])
    ]
    surviving = [item for item in phase_remainders if item[1]]
    combined = dict(basis)
    for row in derivatives[PHASE_INDEX]:
        insert_row(combined, row)

    witness = None
    if surviving:
        output_index, _remainder = surviving[0]
        equations = [(row, 0) for row in basis.values()]
        equations.append((derivatives[PHASE_INDEX][output_index], 1))
        solution = solve_affine(equations, width)
        if solution is None:
            raise AssertionError("phase rank increase had no tangent witness")
        witness = {
            "nonzero_phase_output": divmod(output_index, right_dimension),
            "tangent_support": [
                divmod(index, right_dimension)
                for index in range(width)
                if (solution >> index) & 1
            ],
            "tangent_weight": solution.bit_count(),
        }

    return {
        "left_module": left_module["name"],
        "right_module": right_module["name"],
        "hom_dimension": width,
        "constraint_rank": len(basis),
        "constraint_nullity": width - len(basis),
        "phase_image_dimension": len(combined) - len(basis),
        "nonzero_central_phase_exists": bool(surviving),
        "witness": witness,
    }


def main():
    words = boundary_words()
    source_elements = {}
    for word in words:
        for _factor, matrix in word:
            source_elements[matrix_key(matrix).hex()] = matrix
    source_generators = [
        word[0][1] for _name, word in factor_generators()[:6]
    ]
    for generator in source_generators:
        source_elements[matrix_key(generator).hex()] = generator
    modules = [
        module_record(name, representation, source_elements.values())
        for name, representation in MODULES
    ]
    records = [
        analyze_block(left, right, words, source_generators)
        for left in modules
        for right in modules
    ]
    print(json.dumps({
        "coefficient_ring": "F2[eps]/(eps^2)",
        "modules": [module["name"] for module in modules],
        "centrality_condition":
            "every survivor block intertwines the first A8 chart",
        "ordered_block_records": records,
        "some_nonzero_central_phase_exists": any(
            record["nonzero_central_phase_exists"] for record in records
        ),
    }, indent=2))


if __name__ == "__main__":
    main()
