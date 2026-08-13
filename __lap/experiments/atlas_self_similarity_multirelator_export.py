"""Export the exact phase plus 24 certified-zero atlas classes for PyTorch.

The input is the boundary-only JSON emitted by
`atlas_perfect_overlap_scan.py`.  The exporter reconstructs the honest 64D
A8 representation with the standalone Young-orthogonal implementation, the
exact block-eight relative alignment or an outer-stable certified-zero
alignment, and one cyclic representative of every certified perfect-overlap
class.  No Sage runtime is required.
"""

import argparse
import json

import numpy as np

from atlas_kernel_collision_enumerator import (
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_certified_outer_tangent import (
    representation as outer_permutation_representation,
)
from atlas_self_similarity_global_audit import amplified_alignment, word_value
from atlas_survivor_chart_filling import canonical, encode_word
from atlas_two_chart_search import (
    I4,
    factor_generators,
    gf2_inv,
    inverse,
    matrix_key,
)


CERTIFIED_OUTER_ALIGNMENT = (
    "00000100010000000001000000000001")


def outer(matrix):
    return gf2_inv(matrix).T.copy()


def direct_sum(left, right):
    zero = np.zeros_like(left)
    return np.block([[left, zero], [zero, right]])


def permutation_matrix(images):
    result = np.zeros((len(images), len(images)), dtype=np.complex128)
    for source, target in enumerate(images):
        result[target, source] = 1
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("perfect_overlap_json")
    parser.add_argument("--bundle", required=True)
    parser.add_argument("--relative", required=True)
    parser.add_argument("--multiplicity", type=int, default=1)
    parser.add_argument(
        "--initial-alignment",
        choices=(
            "exact-phase",
            "certified-outer",
            "certified-outer-permutation",
        ),
        default="exact-phase",
    )
    parser.add_argument(
        "--phase-target", choices=("i", "-i", "-1"), default="i")
    parser.add_argument("--include-phase-centrality", action="store_true")
    args = parser.parse_args()
    if args.multiplicity < 1:
        raise ValueError("multiplicity must be positive")
    with open(args.perfect_overlap_json, encoding="utf-8") as stream:
        scan = json.load(stream)
    if scan["radius"] != 5 or not scan["boundary_only"]:
        raise ValueError("expected the complete boundary-only radius-five scan")
    if scan["perfect_overlap_certificates"] != 178:
        raise ValueError("expected 178 certified boundary words")

    states, _level_sizes = enumerate_ball(5)
    kernel_words, _collision_sizes, _depths = spanning_tree_kernel_words(states)
    identity_key = matrix_key(I4)
    boundary = [word for word in kernel_words if any(
        matrix_key(projection) != identity_key
        for projection in factor_projections(word))]
    if len(boundary) != 234:
        raise AssertionError("complete boundary does not have 234 words")

    certified = {}
    for record in scan["certificate_records"]:
        index = record["word_index"]
        key = canonical(encode_word(boundary[index]))
        certified.setdefault(key, (index, boundary[index]))
    representatives = sorted(certified.values())
    if len(representatives) != 24:
        raise AssertionError("certified boundary does not have 24 cyclic classes")

    phase_index = 11
    phase_word = boundary[phase_index]
    words = [word for _index, word in representatives]
    source_indices = [index for index, _word in representatives]
    labels = [f"zero_{index}" for index in source_indices]
    if args.include_phase_centrality:
        for generator_name, generator in factor_generators():
            words.append(
                phase_word + generator + inverse(phase_word)
                + inverse(generator))
            source_indices.append(-len(source_indices))
            labels.append(f"centrality_{generator_name}")
    words.append(phase_word)
    source_indices.append(phase_index)
    labels.append("phase_11")
    phase_targets = {"i": 1j, "-i": -1j, "-1": -1}
    phase_target = phase_targets[args.phase_target]
    targets = np.array(
        [1] * (len(words) - 1) + [phase_target], dtype=np.complex128)
    if len(representatives) != 24 or len(words) < 25:
        raise AssertionError("malformed identity/phase constraint package")
    representation64, phase_relative = amplified_alignment()
    if args.initial_alignment == "exact-phase":
        if phase_target != 1j:
            raise ValueError("the exact-phase alignment has target i only")
        phase_value = word_value(
            boundary[phase_index], representation64, phase_relative)
        if np.linalg.norm(phase_value - 1j * np.eye(64)) > 1e-10:
            raise AssertionError("exported alignment lost the exact phase")
        block_dimension = 64

        def block_representation(matrix):
            return np.asarray(
                representation64(matrix), dtype=np.complex128
            ).reshape(64, 64)

        relative_block = np.asarray(
            phase_relative, dtype=np.complex128).reshape(64, 64)
    elif args.initial_alignment == "certified-outer":
        block_dimension = 128

        def block_representation(matrix):
            return direct_sum(
                np.asarray(
                    representation64(matrix), dtype=np.complex128
                ).reshape(64, 64),
                np.asarray(
                    representation64(outer(matrix)), dtype=np.complex128
                ).reshape(64, 64),
            )

        alignment = np.frombuffer(
            bytes.fromhex(CERTIFIED_OUTER_ALIGNMENT), dtype=np.uint8
        ).reshape(4, 4).copy()
        swap = np.block([
            [np.zeros((64, 64), dtype=np.complex128), np.eye(64)],
            [np.eye(64), np.zeros((64, 64), dtype=np.complex128)],
        ])
        relative_block = block_representation(alignment) @ swap
    else:
        block_dimension = 30

        def block_representation(matrix):
            return permutation_matrix(
                outer_permutation_representation(matrix))

        alignment = np.frombuffer(
            bytes.fromhex(CERTIFIED_OUTER_ALIGNMENT), dtype=np.uint8
        ).reshape(4, 4).copy()
        swap = np.block([
            [np.zeros((15, 15), dtype=np.complex128), np.eye(15)],
            [np.eye(15), np.zeros((15, 15), dtype=np.complex128)],
        ])
        relative_block = block_representation(alignment) @ swap

    multiplicity_identity = np.eye(args.multiplicity, dtype=np.complex128)
    dimension = block_dimension * args.multiplicity
    maximum_length = max(map(len, words))
    block_cache = {}

    def represented_block(matrix):
        key = matrix_key(matrix)
        if key not in block_cache:
            block_cache[key] = block_representation(matrix)
        return block_cache[key]

    block_identity = np.eye(block_dimension, dtype=np.complex128)
    block_relative_adjoint = relative_block.conj().T
    initial_errors = []
    for word_index, word in enumerate(words):
        value = block_identity
        for factor, matrix in word:
            represented = represented_block(matrix)
            if factor == 2:
                represented = (
                    relative_block @ represented @ block_relative_adjoint)
            value = value @ represented
        initial_errors.append(float(np.linalg.norm(
            value - targets[word_index] * block_identity)
            / np.sqrt(block_dimension)))
    if (args.initial_alignment.startswith("certified-outer")
            and max(initial_errors[:24]) > 1e-10):
        raise AssertionError("certified outer alignment did not kill all classes")

    factors = np.zeros((len(words), maximum_length), dtype=np.int8)
    matrices = np.zeros(
        (len(words), maximum_length, dimension, dimension),
        dtype=np.complex128)
    lengths = np.array(list(map(len, words)), dtype=np.int16)
    representation_cache = {}
    for word_index, word in enumerate(words):
        for position, (factor, matrix) in enumerate(word):
            factors[word_index, position] = factor
            key = matrix_key(matrix)
            if key not in representation_cache:
                representation_cache[key] = np.kron(
                    multiplicity_identity, represented_block(matrix))
            matrices[word_index, position] = representation_cache[key]

    relative_array = np.kron(multiplicity_identity, relative_block)
    np.save(args.relative, relative_array)
    np.savez(
        args.bundle,
        factors=factors,
        matrices=matrices,
        lengths=lengths,
        targets=targets,
        source_indices=np.array(source_indices, dtype=np.int32),
        labels=np.array(labels),
    )
    print(json.dumps({
        "certified_words": scan["perfect_overlap_certificates"],
        "certified_cyclic_classes": len(representatives),
        "certified_representative_indices": [
            index for index, _word in representatives],
        "phase_boundary_index": phase_index,
        "phase_target": f"{args.phase_target} I_{dimension}",
        "initial_alignment": args.initial_alignment,
        "certified_zero_classes": 24,
        "centrality_constraints": len(words) - 25,
        "initial_identity_rms": float(np.sqrt(np.mean(
            np.square(initial_errors[:-1])))),
        "initial_identity_max": max(initial_errors[:-1]),
        "initial_certified_zero_rms": float(np.sqrt(np.mean(
            np.square(initial_errors[:24])))),
        "initial_centrality_rms": (
            float(np.sqrt(np.mean(np.square(initial_errors[24:-1]))))
            if args.include_phase_centrality else None),
        "initial_phase_error": initial_errors[-1],
        "multiplicity": args.multiplicity,
        "dimension": dimension,
        "maximum_word_length": maximum_length,
        "bundle": args.bundle,
        "relative": args.relative,
    }, indent=2))


if __name__ == "__main__":
    main()
