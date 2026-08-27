#!/usr/bin/env python3
"""Numerically stress-test the forbidden Wedderburn holonomy constant.

For one forbidden packet copy the two 28-dimensional representations have
commutants

    A_plus  = M_2^4 direct-sum M_3, with multiplicities (2,2,2,2,4),
    A_minus = C^16 direct-sum M_3, with multiplicities (1,...,1,4).

Their Reynolds projections both have rank 25.  The obvious block alignment
has superoperator overlap 17 and normalized squared distance 1/49.  This
script searches U(28) for a larger overlap.  It is a falsification experiment,
not the proof of the bound.
"""
from __future__ import print_function

import json
import numpy as np


def matrix_units(size):
    output = []
    for row in range(size):
        for column in range(size):
            value = np.zeros((size, size), dtype=np.complex128)
            value[row, column] = 1.0
            output.append(value)
    return output


def amplified_factor_basis(irrep_dimension, multiplicity):
    identity = np.eye(irrep_dimension, dtype=np.complex128) / np.sqrt(irrep_dimension)
    return [np.kron(identity, unit) for unit in matrix_units(multiplicity)]


def block_diagonal_basis(block_bases, block_sizes):
    total = sum(block_sizes)
    offsets = np.cumsum([0] + block_sizes)
    output = []
    for block_index, basis in enumerate(block_bases):
        start, stop = offsets[block_index], offsets[block_index + 1]
        for value in basis:
            embedded = np.zeros((total, total), dtype=np.complex128)
            embedded[start:stop, start:stop] = value
            output.append(embedded)
    return np.stack(output)


def build_bases():
    plus_blocks = [amplified_factor_basis(2, 2) for _ in range(4)]
    plus_blocks.append(amplified_factor_basis(4, 3))
    plus_sizes = [4, 4, 4, 4, 12]

    minus_blocks = [amplified_factor_basis(1, 1) for _ in range(16)]
    minus_blocks.append(amplified_factor_basis(4, 3))
    minus_sizes = [1] * 16 + [12]
    plus = block_diagonal_basis(plus_blocks, plus_sizes)
    minus = block_diagonal_basis(minus_blocks, minus_sizes)
    assert plus.shape == minus.shape == (25, 28, 28)
    return plus, minus


def overlap(plus, minus, unitary):
    transported = np.einsum(
        "ij,bjk,lk->bil", unitary, minus, unitary.conjugate(), optimize=True
    )
    gram = np.einsum("aij,bij->ab", plus.conjugate(), transported, optimize=True)
    return float(np.sum(np.abs(gram) ** 2).real)


def haar_unitary(rng, size):
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    q, r = np.linalg.qr(matrix)
    phases = np.diag(r)
    phases = np.where(np.abs(phases) > 0, phases / np.abs(phases), 1.0)
    return q * phases.conjugate()


def near_identity(rng, size, scale):
    perturbation = (
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    perturbation = perturbation - perturbation.conjugate().T
    q, _ = np.linalg.qr(np.eye(size) + scale * perturbation / np.sqrt(size))
    return q


def hill_climb(plus, minus, rng, start, iterations):
    current = start
    current_value = overlap(plus, minus, current)
    best_value = current_value
    accepted = 0
    for iteration in range(iterations):
        fraction = iteration / max(1, iterations - 1)
        scale = 0.20 * (0.01 / 0.20) ** fraction
        candidate = np.dot(near_identity(rng, 28, scale), current)
        value = overlap(plus, minus, candidate)
        if value > current_value + 1e-12:
            current = candidate
            current_value = value
            accepted += 1
            best_value = max(best_value, value)
    return best_value, accepted


def main():
    plus, minus = build_bases()
    rng = np.random.RandomState(20260820)
    identity = np.eye(28, dtype=np.complex128)
    aligned_overlap = overlap(plus, minus, identity)
    assert abs(aligned_overlap - 17.0) < 1e-10

    runs = []
    value, accepted = hill_climb(plus, minus, rng, identity, 1200)
    runs.append({"start": "aligned", "best_overlap": value, "accepted": accepted})
    for restart in range(6):
        start = haar_unitary(rng, 28)
        value, accepted = hill_climb(plus, minus, rng, start, 800)
        runs.append({"start": "haar_%d" % restart, "best_overlap": value, "accepted": accepted})

    maximum = max(run["best_overlap"] for run in runs)
    result = {
        "ambient_dimension": 28,
        "reynolds_ranks": [25, 25],
        "aligned_overlap": aligned_overlap,
        "best_overlap_found": maximum,
        "aligned_normalized_squared_distance": (50.0 - 2.0 * aligned_overlap) / (28.0 ** 2),
        "best_normalized_squared_distance_found": (50.0 - 2.0 * maximum) / (28.0 ** 2),
        "target_lower_bound": 1.0 / 49.0,
        "runs": runs,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
