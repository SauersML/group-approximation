"""Screen rank-three tangent rigidity at the classical A8 atlas alignment.

The 234 first-boundary words vanish at the unique inner alignment ``k0``.
For a permutation representation ``rho`` of ``A8 ~= GL(4,2)``, this script
compares two exact integer Jacobians:

* ``J_B`` is the derivative of all 234 boundary words when only the second
  chart is moved;
* ``J_H`` is the derivative of ``[V,rho(h)]`` at ``V=1`` for four adjacent
  transvections generating ``H = diag(GL(3,2),1)``.

It reports modular ranks of ``J_B`` and ``[J_B;J_H]``.  A rank increase for
even one representation and one prime disproves the proposed infinitesimal
boundary implication ``ker J_B <= ker J_H``.  Equality is only a positive
screen; the regular representation and a characteristic-zero certificate
are still needed for a proof.

Only Gram matrices are formed.  All represented group elements are
permutations, so the calculation is exact over the integers and independent
of multiplicity amplification.
"""

import argparse
import json

import numpy as np

from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_certified_a8_alignment import boundary_words, outer
from atlas_certified_outer_tangent import modular_rank
from atlas_two_chart_search import I4, gf2_inv, gf2_mul


INNER_ALIGNMENT_HEX = "00000100000100000100000000000001"


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
    return tuple(lookup[tuple(((matrix @ vector) & 1).tolist())]
                 for vector in vectors)


def direct_sum(left, right):
    offset = len(left)
    return tuple(list(left) + [offset + value for value in right])


def represented_permutation(matrix, model):
    point = point_permutation(matrix)
    if model == "point15":
        return point
    if model == "point_hyperplane30":
        return direct_sum(point, point_permutation(outer(matrix)))
    raise ValueError("unknown model: %s" % model)


def derivative_terms(word, alignment, alignment_inverse, model):
    """Signed prefix permutations in the right-trivialized derivative."""
    dimension = 15 if model == "point15" else 30
    identity = tuple(range(dimension))
    prefix = identity
    terms = []
    for factor, matrix in word:
        image = matrix
        if factor == 2:
            image = gf2_mul(gf2_mul(
                alignment, matrix), alignment_inverse)
        represented = represented_permutation(image, model)
        before = prefix
        prefix = compose(represented, prefix)
        if factor == 2:
            terms.extend(((1, before), (-1, prefix)))
    return prefix, terms


def add_operator_gram(gram, terms, dimension):
    """Add the exact Gram of ``sum c Ad(permutation)`` to ``gram``."""
    endomorphism_dimension = dimension * dimension
    rows = [{} for _ in range(endomorphism_dimension)]
    for coefficient, permutation in terms:
        for row_index in range(dimension):
            image_row = permutation[row_index]
            for column_index in range(dimension):
                source = dimension * row_index + column_index
                target = dimension * image_row + permutation[column_index]
                rows[target][source] = (
                    rows[target].get(source, 0) + coefficient)
    for row in rows:
        nonzero = [(index, value) for index, value in row.items() if value]
        for left, left_value in nonzero:
            for right, right_value in nonzero:
                gram[left, right] += left_value * right_value


def boundary_gram(words, alignment, alignment_inverse, model):
    dimension = 15 if model == "point15" else 30
    gram = np.zeros((dimension * dimension, dimension * dimension),
                    dtype=np.int64)
    identity = tuple(range(dimension))
    for word in words:
        value, terms = derivative_terms(
            word, alignment, alignment_inverse, model)
        if value != identity:
            raise AssertionError("classical alignment does not kill boundary")
        add_operator_gram(gram, terms, dimension)
    return gram


def h_gram(model):
    dimension = 15 if model == "point15" else 30
    identity = tuple(range(dimension))
    gram = np.zeros((dimension * dimension, dimension * dimension),
                    dtype=np.int64)
    # These adjacent transvections generate diag(GL(3,2),1).
    generators = ((0, 1), (1, 0), (1, 2), (2, 1))
    for row, column in generators:
        matrix = I4.copy()
        matrix[row, column] ^= 1
        represented = represented_permutation(matrix, model)
        add_operator_gram(gram, ((1, identity), (-1, represented)), dimension)
    return gram


def run(model, primes):
    alignment = np.frombuffer(
        bytes.fromhex(INNER_ALIGNMENT_HEX), dtype=np.uint8
    ).reshape(4, 4).copy()
    alignment_inverse = gf2_inv(alignment)
    if not any(np.array_equal(alignment, element)
               for element in enumerate_gl4()):
        raise AssertionError("stored alignment is not in GL(4,2)")
    words = boundary_words()
    boundary = boundary_gram(words, alignment, alignment_inverse, model)
    target = h_gram(model)
    combined = boundary + target
    boundary_ranks = {
        str(prime): modular_rank(boundary, prime) for prime in primes
    }
    combined_ranks = {
        str(prime): modular_rank(combined, prime) for prime in primes
    }
    dimension = 15 if model == "point15" else 30
    return {
        "model": model,
        "representation_dimension": dimension,
        "endomorphism_dimension": dimension * dimension,
        "boundary_relations": len(words),
        "h_generators": 4,
        "boundary_rank_mod_primes": boundary_ranks,
        "boundary_plus_h_rank_mod_primes": combined_ranks,
        "h_variation_rank_on_boundary_tangent": {
            str(prime): combined_ranks[str(prime)]
            - boundary_ranks[str(prime)]
            for prime in primes
        },
        "tangent_inclusion_passes_screen": all(
            combined_ranks[str(prime)] == boundary_ranks[str(prime)]
            for prime in primes
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--models", nargs="+",
        choices=("point15", "point_hyperplane30"),
        default=("point15", "point_hyperplane30"),
    )
    parser.add_argument("--primes", type=int, nargs="+",
                        default=(1000003, 1000033))
    args = parser.parse_args()
    print(json.dumps([
        run(model, args.primes) for model in args.models
    ], indent=2))


if __name__ == "__main__":
    main()
