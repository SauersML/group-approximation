"""Instantiate the 64D self-similarity phase seed in honest A8 charts.

The survivor relation r has local factor groups D8 and V4.  In the
64-dimensional A8 irrep W=(5,2,1), the D8 restriction has sixteen copies of
its faithful two-dimensional irrep and the V4 restriction is sixteen copies
of its regular representation.  This script constructs the relative chart
unitary from spectral projectors, exhausts the six complementary character
assignments, and measures both local and full-chart centrality.

Run with SageMath.  No optimization or random initialization is used.
"""

import argparse
import itertools
import json
import math

import numpy as np

from atlas_clifford_block import CliffordBlock
from atlas_two_chart_search import (
    factor_generators,
    gf2_mul,
    transvection,
)


def projector_basis(projector, tolerance=0.5):
    values, vectors = np.linalg.eigh((projector + projector.conj().T) / 2)
    return vectors[:, values > tolerance]


def joint_bases(first, second):
    identity = np.eye(first.shape[0], dtype=np.complex128)
    answer = {}
    for first_sign, second_sign in itertools.product((-1, 1), repeat=2):
        projector = (
            ((identity + first_sign * first) / 2)
            @ ((identity + second_sign * second) / 2)
        )
        answer[(first_sign, second_sign)] = projector_basis(projector)
    return answer


def commutator_defect(left, right):
    dimension = left.shape[0]
    commutator = left @ right @ left.conj().T @ right.conj().T
    return float(np.linalg.norm(commutator - np.eye(dimension))
                 / math.sqrt(dimension))


def spectral_counts(value):
    roots = (1, -1, 1j, -1j)
    counts = {str(root): 0 for root in roots}
    maximum_error = 0.0
    for eigenvalue in np.linalg.eigvals(value):
        root = min(roots, key=lambda candidate: abs(eigenvalue - candidate))
        counts[str(root)] += 1
        maximum_error = max(maximum_error, abs(eigenvalue - root))
    return counts, float(maximum_error)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--save-best")
    args = parser.parse_args()
    block = CliffordBlock(seed=0)
    representation = block.representation
    identity = np.eye(64, dtype=np.complex128)

    a = transvection(1, 0)
    b = transvection(0, 1)
    c = transvection(1, 2)
    d = gf2_mul(c, b)
    expected_d = np.eye(4, dtype=np.uint8)
    expected_d[0, 1] ^= 1
    expected_d[1, 2] ^= 1
    if not np.array_equal(d, expected_d):
        raise AssertionError("d is not I+E_01+E_12")

    rho_a = representation(a)
    rho_b = representation(b)
    rho_c = representation(c)
    rho_d = representation(d)
    center = (rho_b @ rho_c) @ (rho_b @ rho_c)
    tau_projector = (identity - center) / 2
    plus_projector = (identity + center) / 2
    if projector_basis(tau_projector).shape[1] != 32:
        raise AssertionError("D8 faithful isotypic rank is not 32")

    theta = math.pi / 8
    tau_involution = tau_projector @ (
        math.cos(theta) * rho_b
        + 1j * math.sin(theta) * rho_b @ rho_c
    ) @ tau_projector

    character_projectors = {}
    for b_sign, c_sign in itertools.product((-1, 1), repeat=2):
        character_projectors[(b_sign, c_sign)] = (
            plus_projector
            @ ((identity + b_sign * rho_b) / 2)
            @ ((identity + c_sign * rho_c) / 2)
        )
        if projector_basis(
                character_projectors[(b_sign, c_sign)]).shape[1] != 8:
            raise AssertionError("D8 character multiplicity is not eight")

    source_bases = joint_bases(rho_a, rho_c)
    if any(basis.shape[1] != 16 for basis in source_bases.values()):
        raise AssertionError("V4 restriction is not sixteen regular copies")

    candidates = []
    character_keys = tuple(sorted(character_projectors))
    for positive_negative in itertools.combinations(character_keys, 2):
        positive_negative = set(positive_negative)
        target_a = tau_involution.copy()
        target_c = tau_involution.copy()
        for key, projector in character_projectors.items():
            if key in positive_negative:
                target_a += projector
                target_c -= projector
            else:
                target_a -= projector
                target_c += projector

        target_bases = joint_bases(target_a, target_c)
        source_frame = np.concatenate(
            [source_bases[key] for key in sorted(source_bases)], axis=1)
        target_frame = np.concatenate(
            [target_bases[key] for key in sorted(target_bases)], axis=1)
        relative = target_frame @ source_frame.conj().T
        image_a = relative @ rho_a @ relative.conj().T
        image_c = relative @ rho_c @ relative.conj().T
        conjugacy_error = max(
            np.linalg.norm(image_a - target_a),
            np.linalg.norm(image_c - target_c),
            np.linalg.norm(relative.conj().T @ relative - identity),
        )

        r_value = (image_a @ rho_b @ image_c @ rho_b
                   @ image_a @ rho_b @ image_c @ rho_d)
        counts, spectral_error = spectral_counts(r_value)
        local_values = (rho_b, rho_c, image_a, image_c)
        local_max = max(commutator_defect(r_value, value)
                        for value in local_values)

        named_generators = factor_generators()
        generator_values = []
        for _name, word in named_generators:
            factor, matrix = word[0]
            value = representation(matrix)
            if factor == 2:
                value = relative @ value @ relative.conj().T
            generator_values.append(value)
        full_defects = [commutator_defect(r_value, value)
                        for value in generator_values]
        record = {
            "positive_negative_d8_characters": [list(key)
                                                  for key in sorted(
                                                      positive_negative)],
            "conjugacy_frobenius_error": float(conjugacy_error),
            "spectrum": counts,
            "spectral_root_error": spectral_error,
            "normalized_trace": [
                float((np.trace(r_value) / 64).real),
                float((np.trace(r_value) / 64).imag),
            ],
            "distance_from_identity_squared": float(
                np.linalg.norm(r_value - identity) ** 2 / 64),
            "local_centrality_max": local_max,
            "full_chart_centrality_max": max(full_defects),
            "full_chart_centrality_rms": float(math.sqrt(
                sum(value * value for value in full_defects)
                / len(full_defects))),
            "full_chart_generator_defects": {
                name: defect
                for (name, _word), defect in zip(
                    named_generators, full_defects, strict=True)
            },
        }
        candidates.append((record, relative))

    # All six maxima are exactly 5/4; eigensolver roundoff separates them at
    # the fifteenth decimal place.  Round the primary key so --save-best uses
    # the genuinely smaller RMS complement rather than that meaningless tie.
    candidates.sort(key=lambda item: (
        round(item[0]["full_chart_centrality_max"], 12),
        item[0]["full_chart_centrality_rms"]))
    if args.save_best:
        np.save(args.save_best, candidates[0][1])
    assignments = [record for record, _relative in candidates]
    print(json.dumps({
        "representation": "A8 irrep (5,2,1), dimension 64",
        "relation": "a_2 b_1 c_2 b_1 a_2 b_1 c_2 (cb)_1",
        "assignments_tested": len(assignments),
        "assignments": assignments,
    }, indent=2))


if __name__ == "__main__":
    main()
