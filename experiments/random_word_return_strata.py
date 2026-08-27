"""Probe the entropy-matched random-word-return conjecture.

The random-relator nonhyperlinearity route does *not* predict a uniform
exp(-c n^2) return probability for every tuple: scalar tuples and a fixed
matrix block repeated with growing multiplicity are exact counterexamples to
that naive formulation.  The proposed replacement is that return probability
should be paid for by the metric/moduli complexity of the tuple's generated
matrix algebra / simultaneous-conjugacy stratum.

This script samples four deliberately different strata:

* ``haar``: generic independent Haar unitaries (usually full M_n algebra);
* ``commuting``: generic simultaneously diagonal unitaries;
* ``scalar``: scalar phases times the identity;
* ``repeated``: a fixed d x d Haar tuple tensored with I_m.

For each tuple it estimates the probability that a random reduced word of a
chosen length evaluates inside an HS ball around the identity, and records
simple structure proxies:

* complex dimension of the generated *-algebra;
* dimension of the simultaneous commutant;
* simultaneous-conjugacy orbit dimension n^2-dim(commutant);
* minimum normalized-HS separation on a short free-group ball.

For repeated blocks it also checks, word by word, that normalized-HS distance
is invariant under tensoring with an identity.  Therefore any observed
n-dependence of the return probability in that stratum is numerical noise,
which is a built-in falsification test for dimension-only heuristics.

Example:

    python experiments/random_word_return_strata.py \
        --dimensions 2 4 6 8 --generators 2 --word-length 40 \
        --word-samples 2000 --tuples 3 --epsilon 0.5 --block-size 2

The output is JSON-lines so that later runs can be concatenated and analyzed
without a bespoke parser.
"""

from __future__ import annotations

import argparse
import json
import math
from typing import Iterable, Sequence

import numpy as np


def haar_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    """Sample Haar U(size) by QR factorization of a complex Ginibre matrix."""
    z = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    q, r = np.linalg.qr(z)
    diagonal = np.diag(r)
    phases = np.ones_like(diagonal)
    nonzero = np.abs(diagonal) > 1e-15
    phases[nonzero] = diagonal[nonzero] / np.abs(diagonal[nonzero])
    return q @ np.diag(np.conj(phases))


def normalized_hs(matrix: np.ndarray) -> float:
    return float(np.linalg.norm(matrix, "fro") / math.sqrt(matrix.shape[0]))


def d2(left: np.ndarray, right: np.ndarray) -> float:
    return normalized_hs(left - right)


def random_reduced_word(
    generators: int, length: int, rng: np.random.Generator
) -> tuple[int, ...]:
    """Letters are +/-1,...,+/-generators; adjacent inverses are forbidden."""
    word: list[int] = []
    previous = 0
    alphabet = tuple(range(1, generators + 1)) + tuple(
        -index for index in range(1, generators + 1)
    )
    for _ in range(length):
        choices = alphabet if previous == 0 else tuple(
            letter for letter in alphabet if letter != -previous
        )
        letter = int(rng.choice(choices))
        word.append(letter)
        previous = letter
    return tuple(word)


def evaluate_word(word: Sequence[int], unitaries: Sequence[np.ndarray]) -> np.ndarray:
    size = unitaries[0].shape[0]
    value = np.eye(size, dtype=complex)
    for letter in word:
        unitary = unitaries[abs(letter) - 1]
        value = value @ (unitary if letter > 0 else unitary.conj().T)
    return value


def reduced_words_upto(generators: int, radius: int) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = [tuple()]
    frontier: list[tuple[int, ...]] = [tuple()]
    alphabet = tuple(range(1, generators + 1)) + tuple(
        -index for index in range(1, generators + 1)
    )
    for _ in range(radius):
        next_frontier: list[tuple[int, ...]] = []
        for word in frontier:
            previous = word[-1] if word else 0
            for letter in alphabet:
                if previous and letter == -previous:
                    continue
                extension = word + (letter,)
                words.append(extension)
                next_frontier.append(extension)
        frontier = next_frontier
    return words


def short_ball_min_separation(
    unitaries: Sequence[np.ndarray], radius: int
) -> float:
    words = reduced_words_upto(len(unitaries), radius)
    values = [evaluate_word(word, unitaries) for word in words]
    best = float("inf")
    for left_index, left in enumerate(values):
        for right in values[left_index + 1 :]:
            best = min(best, d2(left, right))
    return best


def commutant_dimension(
    unitaries: Sequence[np.ndarray], singular_tolerance: float
) -> int:
    """Complex dimension of {X : XU_i=U_iX for every i}, numerically."""
    size = unitaries[0].shape[0]
    identity = np.eye(size, dtype=complex)
    blocks = []
    # Column-major vec identity:
    # vec(XU-UX)=(U^T tensor I - I tensor U) vec(X).
    for unitary in unitaries:
        blocks.append(
            np.kron(unitary.T, identity) - np.kron(identity, unitary)
        )
    operator = np.vstack(blocks)
    singular_values = np.linalg.svd(operator, compute_uv=False)
    return int(np.sum(singular_values <= singular_tolerance))


def generated_star_algebra_dimension(
    unitaries: Sequence[np.ndarray], linear_tolerance: float
) -> int:
    """Numerically span the unital *-algebra generated by the tuple."""
    size = unitaries[0].shape[0]
    generators = list(unitaries) + [unitary.conj().T for unitary in unitaries]
    basis: list[np.ndarray] = []
    queue: list[np.ndarray] = []

    def add(matrix: np.ndarray) -> bool:
        candidate = matrix.astype(complex).copy()
        # Two passes make the elementary Gram--Schmidt robust enough for these
        # small diagnostic dimensions without importing scipy.
        for _ in range(2):
            for vector in basis:
                candidate -= np.vdot(vector, candidate) * vector
        norm = np.linalg.norm(candidate, "fro")
        if norm <= linear_tolerance:
            return False
        candidate /= norm
        basis.append(candidate)
        queue.append(candidate)
        return True

    add(np.eye(size, dtype=complex))
    cursor = 0
    while cursor < len(queue) and len(basis) < size * size:
        vector = queue[cursor]
        cursor += 1
        for generator in generators:
            add(vector @ generator)
            if len(basis) == size * size:
                break
    return len(basis)


def tuple_for_mode(
    mode: str,
    size: int,
    generators: int,
    block_size: int,
    rng: np.random.Generator,
) -> tuple[list[np.ndarray], list[np.ndarray] | None]:
    """Return ambient tuple and, for repeated mode, its unamplified base tuple."""
    if mode == "haar":
        return [haar_unitary(size, rng) for _ in range(generators)], None

    if mode == "commuting":
        phases = rng.uniform(-math.pi, math.pi, size=(generators, size))
        return [np.diag(np.exp(1j * row)) for row in phases], None

    if mode == "scalar":
        phases = rng.uniform(-math.pi, math.pi, size=generators)
        identity = np.eye(size, dtype=complex)
        return [np.exp(1j * phase) * identity for phase in phases], None

    if mode == "repeated":
        if size % block_size:
            raise ValueError(
                f"dimension {size} is not divisible by block size {block_size}"
            )
        multiplicity = size // block_size
        base = [haar_unitary(block_size, rng) for _ in range(generators)]
        identity = np.eye(multiplicity, dtype=complex)
        ambient = [np.kron(unitary, identity) for unitary in base]
        return ambient, base

    raise ValueError(f"unknown mode {mode!r}")


def return_statistics(
    unitaries: Sequence[np.ndarray],
    base_unitaries: Sequence[np.ndarray] | None,
    generators: int,
    word_length: int,
    word_samples: int,
    epsilon: float,
    rng: np.random.Generator,
) -> dict[str, float]:
    identity = np.eye(unitaries[0].shape[0], dtype=complex)
    returns = 0
    distances: list[float] = []
    base_distances: list[float] = []

    for _ in range(word_samples):
        word = random_reduced_word(generators, word_length, rng)
        distance = d2(evaluate_word(word, unitaries), identity)
        distances.append(distance)
        returns += int(distance <= epsilon)
        if base_unitaries is not None:
            base_identity = np.eye(base_unitaries[0].shape[0], dtype=complex)
            base_distances.append(
                d2(evaluate_word(word, base_unitaries), base_identity)
            )

    probability = returns / word_samples
    result = {
        "return_probability": probability,
        "return_log_cost": float("inf") if probability == 0 else -math.log(probability),
        "mean_word_distance": float(np.mean(distances)),
        "min_word_distance": float(np.min(distances)),
    }
    if base_distances:
        error = np.max(np.abs(np.asarray(distances) - np.asarray(base_distances)))
        result["repeated_block_distance_invariance_error"] = float(error)
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimensions", type=int, nargs="+", default=[2, 4, 6, 8])
    parser.add_argument("--generators", type=int, default=2)
    parser.add_argument("--word-length", type=int, default=40)
    parser.add_argument("--word-samples", type=int, default=1000)
    parser.add_argument("--tuples", type=int, default=2)
    parser.add_argument("--epsilon", type=float, default=0.5)
    parser.add_argument("--block-size", type=int, default=2)
    parser.add_argument("--separation-radius", type=int, default=2)
    parser.add_argument("--singular-tolerance", type=float, default=1e-8)
    parser.add_argument("--linear-tolerance", type=float, default=1e-9)
    parser.add_argument("--seed", type=int, default=20260818)
    parser.add_argument(
        "--modes",
        nargs="+",
        choices=("haar", "commuting", "scalar", "repeated"),
        default=["haar", "commuting", "scalar", "repeated"],
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rng = np.random.default_rng(args.seed)

    for size in args.dimensions:
        for mode in args.modes:
            if mode == "repeated" and size % args.block_size:
                continue
            for sample in range(args.tuples):
                unitaries, base = tuple_for_mode(
                    mode,
                    size,
                    args.generators,
                    args.block_size,
                    rng,
                )
                algebra_dimension = generated_star_algebra_dimension(
                    unitaries, args.linear_tolerance
                )
                commutant_dimension_value = commutant_dimension(
                    unitaries, args.singular_tolerance
                )
                row = {
                    "mode": mode,
                    "dimension": size,
                    "tuple_sample": sample,
                    "generators": args.generators,
                    "word_length": args.word_length,
                    "word_samples": args.word_samples,
                    "epsilon": args.epsilon,
                    "generated_star_algebra_dimension": algebra_dimension,
                    "commutant_dimension": commutant_dimension_value,
                    "simultaneous_conjugacy_orbit_dimension": (
                        size * size - commutant_dimension_value
                    ),
                    "short_ball_min_separation": short_ball_min_separation(
                        unitaries, args.separation_radius
                    ),
                }
                row.update(
                    return_statistics(
                        unitaries,
                        base,
                        args.generators,
                        args.word_length,
                        args.word_samples,
                        args.epsilon,
                        rng,
                    )
                )
                print(json.dumps(row, sort_keys=True))


if __name__ == "__main__":
    main()
