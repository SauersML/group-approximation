"""Linearize the 24 certified atlas relations at the outer A8 quotient.

The model is the outer-stable sum of the 15-point action of GL(4,2) and its
outer twist.  All matrices are permutations, so the Jacobian Gram matrix has
integer entries.  Modular ranks give exact lower bounds; ``--gap`` emits a
GAP program computing the characteristic-zero ranks exactly.
"""

import argparse
import json

import numpy as np

from atlas_certified_a8_alignment import (
    CERTIFIED_REPRESENTATIVE_INDICES,
    PHASE_INDEX,
    boundary_words,
    outer,
)
from atlas_two_chart_search import gf2_inv, gf2_mul


OUTER_ALIGNMENT = "00000100010000000001000000000001"
DIMENSION = 30
ENDOMORPHISM_DIMENSION = DIMENSION * DIMENSION


def compose(left, right):
    """Permutation of a matrix product in the column-action convention."""
    return tuple(right[left[index]] for index in range(len(left)))


def point_permutation(matrix):
    vectors = [
        np.array([(value >> bit) & 1 for bit in range(4)], dtype=np.uint8)
        for value in range(1, 16)
    ]
    lookup = {tuple(vector.tolist()): index
              for index, vector in enumerate(vectors)}
    return tuple(lookup[tuple(((matrix @ vector) % 2).tolist())]
                 for vector in vectors)


def direct_sum(left, right):
    return tuple(list(left) + [15 + value for value in right])


def representation(matrix):
    return direct_sum(
        point_permutation(matrix), point_permutation(outer(matrix)))


def aligned_representation(matrix, alignment, alignment_inverse):
    image = gf2_mul(gf2_mul(
        alignment, outer(matrix)), alignment_inverse)
    return representation(image)


def derivative_terms(word, alignment, alignment_inverse):
    """Return signed prefix permutations in the right-trivialized derivative."""
    identity = tuple(range(DIMENSION))
    prefix = identity
    terms = []
    for factor, matrix in word:
        represented = (
            representation(matrix) if factor == 1
            else aligned_representation(
                matrix, alignment, alignment_inverse)
        )
        before = prefix
        prefix = compose(represented, prefix)
        if factor == 2:
            terms.extend(((1, before), (-1, prefix)))
    return prefix, terms


def jacobian_gram(
        words, alignment, alignment_inverse, *, require_identity=True):
    gram = np.zeros(
        (ENDOMORPHISM_DIMENSION, ENDOMORPHISM_DIMENSION),
        dtype=np.int64,
    )
    identity = tuple(range(DIMENSION))
    for word in words:
        value, terms = derivative_terms(
            word, alignment, alignment_inverse)
        if require_identity and value != identity:
            raise AssertionError("base point does not satisfy a zero relation")
        rows = [{} for _ in range(ENDOMORPHISM_DIMENSION)]
        for coefficient, permutation in terms:
            for row_index in range(DIMENSION):
                image_row = permutation[row_index]
                for column_index in range(DIMENSION):
                    source = DIMENSION * row_index + column_index
                    target = (DIMENSION * image_row
                              + permutation[column_index])
                    rows[target][source] = (
                        rows[target].get(source, 0) + coefficient)
        for row in rows:
            nonzero = [(index, value) for index, value in row.items() if value]
            for left, left_value in nonzero:
                for right, right_value in nonzero:
                    gram[left, right] += left_value * right_value
    return gram


def modular_rank(matrix, prime):
    reduced = np.remainder(matrix.copy(), prime)
    row_count, column_count = reduced.shape
    rank = 0
    for column in range(column_count):
        candidates = np.flatnonzero(reduced[rank:, column])
        if not len(candidates):
            continue
        pivot = rank + int(candidates[0])
        reduced[[rank, pivot]] = reduced[[pivot, rank]]
        inverse = pow(int(reduced[rank, column]), prime - 2, prime)
        reduced[rank] = np.remainder(reduced[rank] * inverse, prime)
        following = np.flatnonzero(reduced[rank + 1:, column]) + rank + 1
        if len(following):
            reduced[following] = np.remainder(
                reduced[following]
                - reduced[following, column, None] * reduced[rank],
                prime,
            )
        rank += 1
        if rank == row_count:
            break
    return rank


def gap_matrix(name, matrix):
    print(f"{name}:=Matrix(Rationals,[")
    for row in matrix:
        print("[%s]," % ",".join(map(str, row.tolist())))
    print("]);;")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--gap", action="store_true",
        help="emit GAP code for exact characteristic-zero ranks",
    )
    args = parser.parse_args()
    alignment = np.frombuffer(
        bytes.fromhex(OUTER_ALIGNMENT), dtype=np.uint8
    ).reshape(4, 4).copy()
    alignment_inverse = gf2_inv(alignment)
    boundary = boundary_words()
    zero_words = [
        boundary[index] for index in CERTIFIED_REPRESENTATIVE_INDICES
    ]
    zero_gram = jacobian_gram(
        zero_words, alignment, alignment_inverse)

    phase_value, _ = derivative_terms(
        boundary[PHASE_INDEX], alignment, alignment_inverse)
    if phase_value == tuple(range(DIMENSION)):
        raise AssertionError("phase unexpectedly vanished")
    if compose(phase_value, phase_value) != tuple(range(DIMENSION)):
        raise AssertionError("phase is not an involution")
    phase_gram = jacobian_gram(
        [boundary[PHASE_INDEX]], alignment, alignment_inverse,
        require_identity=False)
    combined_gram = zero_gram + phase_gram

    if args.gap:
        gap_matrix("zeroGram", zero_gram)
        gap_matrix("combinedGram", combined_gram)
        print('Print("zero_rank_Q ",RankMat(zeroGram),"\\n");')
        print('Print("combined_rank_Q ",RankMat(combinedGram),"\\n");')
        print("QUIT;")
        return

    primes = (1000003, 1000033)
    zero_ranks = {
        str(prime): modular_rank(zero_gram, prime) for prime in primes
    }
    combined_ranks = {
        str(prime): modular_rank(combined_gram, prime) for prime in primes
    }
    print(json.dumps({
        "representation_dimension": DIMENSION,
        "endomorphism_dimension": ENDOMORPHISM_DIMENSION,
        "certified_zero_relations": len(zero_words),
        "phase_boundary_index": PHASE_INDEX,
        "phase_is_identity": False,
        "phase_order": 2,
        "zero_jacobian_rank_mod_primes": zero_ranks,
        "zero_tangent_nullity_upper_bound": {
            prime: ENDOMORPHISM_DIMENSION - rank
            for prime, rank in zero_ranks.items()
        },
        "zero_plus_phase_jacobian_rank_mod_primes": combined_ranks,
        "phase_variation_rank_on_zero_tangent_lower_bound": {
            prime: combined_ranks[prime] - zero_ranks[prime]
            for prime in zero_ranks
        },
    }, indent=2))


if __name__ == "__main__":
    main()
