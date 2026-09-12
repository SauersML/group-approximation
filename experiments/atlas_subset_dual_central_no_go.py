"""Exhaust dual-number central phases in the Boolean A8 permutation modules.

For the actions of A8 on k-subsets of eight points, k=1,2,3,4, linearize
the inner-aligned two-chart atlas over F_2[eps]/(eps^2).  Exact bitset row
reduction proves that the 24 certified-zero classes plus centrality of the
four survivor classes force the scalar coefficient of phase class 11 to
vanish.  Complementation covers k=5,6,7.
"""

from itertools import combinations
import json

from atlas_certified_a8_alignment import (
    CERTIFIED_REPRESENTATIVE_INDICES,
    PHASE_INDEX,
    boundary_words,
)
from atlas_certified_dual_number_certificate import (
    ALIGNMENT_KEY,
    chart_images,
    evaluate,
    natural_a8_map,
    pair_equal,
    pair_mul,
)
from atlas_two_chart_search import factor_generators, matrix_key


SURVIVOR_REPRESENTATIVES = (11, 30, 44, 55)
EXPECTED_RANKS = {1: 61, 2: 768, 3: 3101, 4: 4839}


def compose(left, right):
    """Composition in the atlas column-action convention."""
    return tuple(right[left[index]] for index in range(len(left)))


def inverse(permutation):
    result = [0] * len(permutation)
    for source, target in enumerate(permutation):
        result[target] = source
    return tuple(result)


def subset_action(permutation, subsets, lookup):
    return tuple(lookup[tuple(sorted(permutation[index] for index in subset))]
                 for subset in subsets)


def word_derivative_rows(
        word, represented, alignment, alignment_inverse, dimension):
    """Rows of the F_2-linear right-trivialized word derivative."""
    identity = tuple(range(dimension))
    prefix = identity
    terms = []
    for factor, matrix in word:
        permutation = represented[matrix_key(matrix).hex()]
        if factor == 2:
            permutation = compose(
                compose(alignment_inverse, permutation), alignment)
        before = prefix
        prefix = compose(permutation, prefix)
        if factor == 2:
            # Minus equals plus in characteristic two.
            terms.extend((before, prefix))
    if prefix != identity:
        raise AssertionError("the inner base alignment stopped killing a word")

    endomorphism_dimension = dimension * dimension
    rows = [0] * endomorphism_dimension
    for permutation in terms:
        for source_row in range(dimension):
            target_row = permutation[source_row]
            row_offset = dimension * source_row
            target_offset = dimension * target_row
            for source_column in range(dimension):
                source = row_offset + source_column
                target = target_offset + permutation[source_column]
                rows[target] ^= 1 << source
    return rows


def insert_row(basis, row):
    """Insert one binary row into a highest-pivot echelon basis."""
    while row:
        pivot = row.bit_length() - 1
        if pivot in basis:
            row ^= basis[pivot]
        else:
            basis[pivot] = row
            return True
    return False


def reduce_row(basis, row):
    while row:
        pivot = row.bit_length() - 1
        if pivot not in basis:
            return row
        row ^= basis[pivot]
    return 0


def analyze_subset_degree(degree, images, words):
    subsets = tuple(combinations(range(8), degree))
    lookup = {subset: index for index, subset in enumerate(subsets)}
    dimension = len(subsets)
    represented = {
        key: subset_action(permutation, subsets, lookup)
        for key, permutation in images.items()
    }
    alignment = represented[ALIGNMENT_KEY]
    alignment_inverse = inverse(alignment)
    selected = sorted(set(
        CERTIFIED_REPRESENTATIVE_INDICES + SURVIVOR_REPRESENTATIVES))
    derivatives = {
        index: word_derivative_rows(
            words[index], represented, alignment, alignment_inverse, dimension)
        for index in selected
    }

    basis = {}
    equation_count = 0
    for index in CERTIFIED_REPRESENTATIVE_INDICES:
        for row in derivatives[index]:
            insert_row(basis, row)
            equation_count += 1

    for index in SURVIVOR_REPRESENTATIVES:
        rows = derivatives[index]
        for row_index in range(dimension):
            for column_index in range(dimension):
                if row_index != column_index:
                    insert_row(
                        basis, rows[dimension * row_index + column_index])
                    equation_count += 1
        for diagonal_index in range(1, dimension):
            insert_row(
                basis,
                rows[dimension * diagonal_index + diagonal_index] ^ rows[0],
            )
            equation_count += 1

    phase_scalar_row = derivatives[PHASE_INDEX][0]
    phase_remainder = reduce_row(basis, phase_scalar_row)
    rank = len(basis)
    if rank != EXPECTED_RANKS[degree]:
        raise AssertionError("Boolean-module constraint rank changed")
    if phase_remainder:
        raise AssertionError("a nonzero scalar phase unexpectedly survives")
    return {
        "subset_degree": degree,
        "representation_dimension": dimension,
        "endomorphism_dimension": dimension * dimension,
        "equations_before_deduplication": equation_count,
        "constraint_rank_over_f2": rank,
        "constraint_nullity_over_f2": dimension * dimension - rank,
        "phase_scalar_row_is_in_constraint_span": True,
        "nonzero_first_order_scalar_phase_exists": False,
    }


def finite_image_obstruction(images, words):
    """Check that centralizing class 30 kills phase in the positive image."""
    first, second, identity, zero, _tangent = chart_images(images)
    class_30 = evaluate(words[30], first, second, identity, zero)
    phase = evaluate(words[PHASE_INDEX], first, second, identity, zero)
    generator_name, generator_word = factor_generators()[0]
    generator = first[matrix_key(generator_word[0][1]).hex()]
    commutator = (identity, zero)
    # Both class_30 and this transvection are involutions, so [a,g] is agag.
    for value in (class_30, generator, class_30, generator):
        commutator = pair_mul(commutator, value)
    if not pair_equal(commutator, phase):
        raise AssertionError("the finite-image commutator obstruction changed")
    return {
        "survivor_representative": 30,
        "first_chart_generator": generator_name,
        "class_30_tangent_diagonal":
            tuple(int(entry) for entry in class_30[1].diagonal()),
        "commutator_equals_phase_11": True,
        "consequence": "centralizing class 30 kills phase 11",
    }


def main():
    images = natural_a8_map()
    words = boundary_words()
    records = [
        analyze_subset_degree(degree, images, words)
        for degree in range(1, 5)
    ]
    print(json.dumps({
        "coefficient_ring": "F2[eps]/(eps^2)",
        "alignment_f2_hex": ALIGNMENT_KEY,
        "certified_zero_representatives":
            CERTIFIED_REPRESENTATIVE_INDICES,
        "central_survivor_representatives": SURVIVOR_REPRESENTATIVES,
        "phase_representative": PHASE_INDEX,
        "subset_module_records": records,
        "degrees_5_6_7_follow_by_complementation": True,
        "positive_finite_image_obstruction":
            finite_image_obstruction(images, words),
    }, indent=2))


if __name__ == "__main__":
    main()
