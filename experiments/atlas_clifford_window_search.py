"""Test simultaneous Clifford repair of the shortest atlas parity window.

This script constructs the 64-dimensional A8 Specht representation of shape
(5,2,1) from Young's orthogonal form.  It then realizes the exact Pauli block
from notes/FALSE_LOCAL_CLIFFORD_ATLAS.md and evaluates every shortest
one-sided tensor-flip failure in that same pair of A8 charts.

The calculation is a discovery/audit tool.  A zero scalarity defect is an
exact algebraic target that must still be certified symbolically; a nonzero
defect only rules out the particular eigenbasis alignment chosen here.
"""

import itertools
import json
import sys

import numpy as np

sys.path.insert(0, "experiments")

from atlas_kernel_collision_enumerator import (  # noqa: E402
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import (  # noqa: E402
    I4,
    gf2_inv,
    gf2_mul,
    matrix_key,
    transvection,
)


SHAPE = (5, 2, 1)


def tableaux():
    """Return the 64 standard tableaux of shape (5,2,1)."""
    out = []
    numbers = set(range(1, 9))
    for first in itertools.combinations(range(1, 9), 5):
        remaining = numbers.difference(first)
        for second in itertools.combinations(sorted(remaining), 2):
            third = tuple(remaining.difference(second))
            rows = (tuple(sorted(first)), tuple(sorted(second)), third)
            if (rows[0][0] < rows[1][0] < rows[2][0]
                    and rows[0][1] < rows[1][1]):
                out.append(rows)
    if len(out) != 64:
        raise AssertionError("hook-length dimension is not 64")
    return out


def adjacent_matrices(tabs):
    """Young orthogonal matrices for (i,i+1), i=1,...,7."""
    indices = {rows: index for index, rows in enumerate(tabs)}
    positions = []
    for rows in tabs:
        position = {}
        for row, entries in enumerate(rows):
            for col, value in enumerate(entries):
                position[value] = (row, col)
        positions.append(position)

    matrices = []
    for value in range(1, 8):
        matrix = np.zeros((64, 64), dtype=np.float64)
        for index, rows in enumerate(tabs):
            row_a, col_a = positions[index][value]
            row_b, col_b = positions[index][value + 1]
            if row_a == row_b:
                matrix[index, index] = 1.0
            elif col_a == col_b:
                matrix[index, index] = -1.0
            else:
                axial = (col_b - row_b) - (col_a - row_a)
                matrix[index, index] = 1.0 / axial
                swapped = [list(row) for row in rows]
                swapped[row_a][col_a] = value + 1
                swapped[row_b][col_b] = value
                target = indices[tuple(tuple(row) for row in swapped)]
                matrix[target, index] = np.sqrt(1.0 - 1.0 / axial**2)
        matrices.append(matrix)

    identity = np.eye(64)
    for index, matrix in enumerate(matrices):
        if np.linalg.norm(matrix @ matrix - identity) > 1e-11:
            raise AssertionError("bad adjacent involution %d" % index)
    for index in range(6):
        left = matrices[index] @ matrices[index + 1]
        if np.linalg.norm(left @ left @ left - identity) > 1e-11:
            raise AssertionError("bad braid relation %d" % index)
    return matrices


def permutation_matrix(permutation, adjacent):
    """Evaluate a one-line permutation using adjacent domain swaps."""
    current = list(range(1, 9))
    word = []
    for position, desired in enumerate(permutation):
        location = current.index(desired)
        while location > position:
            current[location - 1], current[location] = (
                current[location], current[location - 1])
            word.append(location - 1)
            location -= 1
    if tuple(current) != tuple(permutation):
        raise AssertionError("permutation decomposition failed")
    value = np.eye(64)
    for generator in word:
        value = value @ adjacent[generator]
    return value


def a8_representation():
    """Enumerate GL(4,2) and its 64-dimensional A8 representation."""
    with open("experiments/atlas-a8-natural.json", "r",
              encoding="utf-8") as stream:
        permutations = json.load(stream)["matrices"]
    generators = [transvection(*pair) for pair in (
        (0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2))]
    adjacent = adjacent_matrices(tableaux())
    generator_reps = [permutation_matrix(
        permutations[matrix_key(generator).hex()], adjacent)
        for generator in generators]

    elements = [I4.copy()]
    indices = {matrix_key(I4): 0}
    reps = [np.eye(64)]
    cursor = 0
    while cursor < len(elements):
        element = elements[cursor]
        rep = reps[cursor]
        cursor += 1
        for generator, generator_rep in zip(generators, generator_reps):
            target = gf2_mul(element, generator)
            target_rep = rep @ generator_rep
            key = matrix_key(target)
            if key not in indices:
                indices[key] = len(elements)
                elements.append(target)
                reps.append(target_rep)
            elif np.linalg.norm(reps[indices[key]] - target_rep) > 2e-9:
                raise AssertionError("A8 representation failed a relation")
    if len(elements) != 20160:
        raise AssertionError("GL(4,2) enumeration failed")
    return indices, reps


def pauli_target(first_s, first_t):
    """Transport X tensor I through W|S3 ~= sigma tensor alpha."""
    pauli_x = np.array([[0, 1], [1, 0]], dtype=np.complex128)
    pauli_y = np.array([[0, -1j], [1j, 0]], dtype=np.complex128)
    pauli_z = np.array([[1, 0], [0, -1]], dtype=np.complex128)
    target_s = (pauli_x + pauli_y) / np.sqrt(2.0)
    target_t = -(pauli_x + pauli_z) / np.sqrt(2.0)
    alpha_s = np.zeros((32, 32), dtype=np.complex128)
    alpha_t = np.zeros((32, 32), dtype=np.complex128)
    alpha_s[:12, :12] = np.eye(12)
    alpha_t[:12, :12] = np.eye(12)
    for copy in range(10):
        start = 12 + 2 * copy
        alpha_s[start:start + 2, start:start + 2] = target_s
        alpha_t[start:start + 2, start:start + 2] = target_t
    model_s = np.kron(target_s, alpha_s)
    model_t = np.kron(target_t, alpha_t)

    source_group = [
        np.eye(64), first_s, first_t, first_s @ first_t,
        first_t @ first_s, first_s @ first_t @ first_s,
    ]
    model_group = [
        np.eye(64), model_s, model_t, model_s @ model_t,
        model_t @ model_s, model_s @ model_t @ model_s,
    ]
    rng = np.random.default_rng(0)
    intertwiner = None
    for _ in range(20):
        seed = (rng.standard_normal((64, 64))
                + 1j * rng.standard_normal((64, 64)))
        candidate = sum(source @ seed @ model.conj().T
                        for source, model in zip(source_group, model_group))
        left, singular, right = np.linalg.svd(candidate)
        if singular[-1] > 1e-8:
            intertwiner = left @ right
            break
    if intertwiner is None:
        raise AssertionError("failed to construct the S3 intertwiner")
    if (np.linalg.norm(first_s @ intertwiner - intertwiner @ model_s) > 1e-8
            or np.linalg.norm(first_t @ intertwiner
                              - intertwiner @ model_t) > 1e-8):
        raise AssertionError("bad S3 tensor-factor intertwiner")
    return intertwiner @ np.kron(pauli_x, np.eye(32)) @ intertwiner.conj().T


def conjugating_unitary(source, target, reference=None):
    """Choose U source U*=target, optionally nearest a reference unitary."""
    source_values, source_vectors = np.linalg.eigh(source)
    target_values, target_vectors = np.linalg.eigh(target)
    if np.linalg.norm(source_values - target_values) > 1e-9:
        raise AssertionError("involutions do not have the same spectrum")
    if reference is None:
        return target_vectors @ source_vectors.conj().T
    half = source.shape[0] // 2
    blocks = []
    for start, stop in ((0, half), (half, source.shape[0])):
        source_block = source_vectors[:, start:stop]
        target_block = target_vectors[:, start:stop]
        overlap = source_block.conj().T @ reference.conj().T @ target_block
        left, _, right = np.linalg.svd(overlap)
        blocks.append(target_block @ (right.conj().T @ left.conj().T)
                      @ source_block.conj().T)
    unitary = sum(blocks)
    if np.linalg.norm(unitary @ source @ unitary.conj().T - target) > 1e-8:
        raise AssertionError("reference Procrustes alignment failed")
    return unitary


def inversion_count(word):
    return sum(1 for index, (factor, _) in enumerate(word)
               for later_factor, _ in word[index + 1:]
               if factor > later_factor)


def main():
    indices, reps = a8_representation()

    s = I4.copy()
    s[[0, 1]] = s[[1, 0]]
    t = transvection(1, 0)
    b = transvection(0, 1)
    st = gf2_mul(s, t)
    first_s = reps[indices[matrix_key(s)]]
    first_t = reps[indices[matrix_key(t)]]
    target_b = pauli_target(first_s, first_t)
    source_b = reps[indices[matrix_key(b)]]
    reference_k = bytes.fromhex("00000100000100000000000101000000")
    reference_d = bytes.fromhex("01000000000100000000010001000001")
    reference = reps[indices[reference_k]] @ (
        np.eye(64) - 1j * reps[indices[reference_d]]) / np.sqrt(2)
    unitary = conjugating_unitary(source_b, target_b, reference)

    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    identity_key = matrix_key(I4)
    shortest = []
    for word in words:
        projections = factor_projections(word)
        one_sided = ((matrix_key(projections[0]) == identity_key)
                     ^ (matrix_key(projections[1]) == identity_key))
        if len(word) == 6 and inversion_count(word) == 3 and one_sided:
            shortest.append(word)

    classical_alignments = []
    for key, group_index in indices.items():
        alignment = np.frombuffer(key, dtype=np.uint8).reshape(4, 4)
        alignment_inverse = gf2_inv(alignment)
        valid = True
        for word in shortest:
            value = I4.copy()
            for factor, matrix in word:
                image = (matrix if factor == 1 else gf2_mul(
                    gf2_mul(alignment, matrix), alignment_inverse))
                value = gf2_mul(value, image)
            if matrix_key(value) != identity_key:
                valid = False
                break
        if valid:
            classical_alignments.append((alignment, group_index))
    print("classical_alignments", len(classical_alignments))

    conjugate_images = []
    for alignment, _ in classical_alignments:
        image = gf2_mul(gf2_mul(alignment, b), gf2_inv(alignment))
        conjugate_images.append(
            reps[indices[matrix_key(image)]].astype(np.complex128))
    coefficients, _, _, _ = np.linalg.lstsq(
        np.stack([value.reshape(-1) for value in conjugate_images], axis=1),
        target_b.reshape(-1), rcond=None)
    image_residual = np.linalg.norm(
        sum(coefficient * value for coefficient, value
            in zip(coefficients, conjugate_images)) - target_b) / 8.0
    print("target_b_classical_image_span_residual", image_residual)

    def evaluate(word, relative_unitary):
        value = np.eye(64, dtype=np.complex128)
        for factor, matrix in word:
            image = reps[indices[matrix_key(matrix)]].astype(np.complex128)
            if factor == 2:
                image = (relative_unitary @ image
                         @ relative_unitary.conj().T)
            value = value @ image
        return value

    square_root_candidates = []
    for left_matrix, left_index in classical_alignments:
        for right_matrix, _ in classical_alignments:
            difference = gf2_mul(gf2_inv(left_matrix), right_matrix)
            if (matrix_key(difference) == identity_key
                    or matrix_key(gf2_mul(difference, difference))
                    != identity_key):
                continue
            difference_rep = reps[indices[matrix_key(difference)]]
            for sign in (-1, 1):
                root = (np.eye(64) + sign * 1j * difference_rep) / np.sqrt(2)
                candidate = reps[left_index] @ root
                scalarities = []
                traces = []
                for word in shortest:
                    value = evaluate(word, candidate)
                    trace = np.trace(value) / 64.0
                    traces.append(trace)
                    scalarities.append(np.linalg.norm(
                        value - trace * np.eye(64)) / 8.0)
                square_root_candidates.append((
                    max(scalarities), sum(value**2 for value in scalarities),
                    left_index, matrix_key(difference).hex(), sign,
                    scalarities, traces))
    print("square_root_candidates", len(square_root_candidates))
    for candidate in sorted(square_root_candidates)[:10]:
        print("square_root_score", candidate[:5],
              "scalar_words", sum(value < 1e-9 for value in candidate[5]),
              "nonscalar", [index for index, value
                            in enumerate(candidate[5]) if value >= 1e-9])

    q = [
        (1, s), (2, b), (1, t), (2, b),
        (1, gf2_mul(st, st)), (2, b),
    ]
    q_value = evaluate(q, unitary)
    print("local_q_phase", np.trace(q_value) / 64.0)
    print("local_q_scalarity", np.linalg.norm(
        q_value - np.trace(q_value) * np.eye(64) / 64.0) / 8.0)

    defects = []
    for index, word in enumerate(shortest):
        value = evaluate(word, unitary)
        trace = np.trace(value) / 64.0
        scalarity = np.linalg.norm(value - trace * np.eye(64)) / 8.0
        defects.append((scalarity, index, trace))
    print("shortest_words", len(shortest))
    print("scalar_words", sum(value < 1e-9 for value, _, _ in defects))
    for scalarity, index, trace in sorted(defects, reverse=True):
        print(index, "scalarity", scalarity, "trace", trace)


if __name__ == "__main__":
    main()
