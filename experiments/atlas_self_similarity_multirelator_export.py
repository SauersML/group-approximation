"""Export the exact phase plus 24 certified-zero atlas classes for PyTorch.

The input is the boundary-only JSON emitted by
`atlas_perfect_overlap_scan.py`.  The exporter reconstructs the honest 64D
A8 representation with the standalone Young-orthogonal implementation, the
exact block-eight relative alignment, and one cyclic representative of every
certified perfect-overlap class.  No Sage runtime is required.
"""

import argparse
import json

import numpy as np

from atlas_kernel_collision_enumerator import (
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_self_similarity_global_audit import amplified_alignment, word_value
from atlas_survivor_chart_filling import canonical, encode_word
from atlas_two_chart_search import I4, matrix_key


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("perfect_overlap_json")
    parser.add_argument("--bundle", required=True)
    parser.add_argument("--relative", required=True)
    parser.add_argument("--multiplicity", type=int, default=1)
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
    words = [word for _index, word in representatives] + [boundary[phase_index]]
    source_indices = [index for index, _word in representatives] + [phase_index]
    targets = np.array([1] * len(representatives) + [1j], dtype=np.complex128)
    if len(words) != 25:
        raise AssertionError("expected 24 zero classes plus one phase class")
    representation, relative = amplified_alignment()
    phase_value = word_value(boundary[phase_index], representation, relative)
    if np.linalg.norm(phase_value - 1j * np.eye(64)) > 1e-10:
        raise AssertionError("exported alignment lost the exact phase")

    multiplicity_identity = np.eye(args.multiplicity, dtype=np.complex128)
    dimension = 64 * args.multiplicity
    maximum_length = max(map(len, words))
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
                represented = np.asarray(
                    representation(matrix), dtype=np.complex128).reshape(64, 64)
                representation_cache[key] = np.kron(
                    multiplicity_identity, represented)
            matrices[word_index, position] = representation_cache[key]

    relative_block = np.asarray(
        relative, dtype=np.complex128).reshape(64, 64)
    relative_array = np.kron(multiplicity_identity, relative_block)
    np.save(args.relative, relative_array)
    np.savez(
        args.bundle,
        factors=factors,
        matrices=matrices,
        lengths=lengths,
        targets=targets,
        source_indices=np.array(source_indices, dtype=np.int32),
    )
    print(json.dumps({
        "certified_words": scan["perfect_overlap_certificates"],
        "certified_cyclic_classes": len(representatives),
        "certified_representative_indices": source_indices[:-1],
        "phase_boundary_index": phase_index,
        "phase_target": f"i I_{dimension}",
        "multiplicity": args.multiplicity,
        "dimension": dimension,
        "maximum_word_length": maximum_length,
        "bundle": args.bundle,
        "relative": args.relative,
    }, indent=2))


if __name__ == "__main__":
    main()
