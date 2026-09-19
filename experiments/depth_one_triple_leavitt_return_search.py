"""Exact all-position search for three depth-one Leavitt root excursions.

This extends ``depth_one_paired_leavitt_return_search.py``.  The original
one-row brute-force attempt stopped at an arbitrary survivor cap.  Here the
conjugation geometry gives an exact filter: conjugating a matrix by an
elementary root ``x_(target,source)(c)`` changes only the target row and the
source column.  Therefore a candidate third root is impossible whenever a
nonconstant entry of a pair-conjugated Hecke generator lies outside that
row/column cross.

The remaining candidates are checked against all ten signed-Hecke generators
in the faithful binary-prefix normal form.  The 304 individually nonnormal
roots give 304^3 ordered triples.  Their first two factors collapse to 54,897
exact symbolic matrices, so checking one representative of each pair product
checks all 28,094,464 ordered triples.

Run from the repository root with

    python3 experiments/depth_one_triple_leavitt_return_search.py
"""

from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import depth_one_paired_leavitt_return_search as base  # noqa: E402


# The exact prefix operations repeat heavily in the triple search.  Replacing
# the module globals by memoized wrappers preserves the implementation while
# making the exhaustive calculation practical.
base.add = lru_cache(maxsize=None)(base.add)
base.multiply = lru_cache(maxsize=None)(base.multiply)
base.constant_bit = lru_cache(maxsize=None)(base.constant_bit)


def matrix_key(matrix):
    """Hashable exact matrix key in the faithful prefix normal form."""

    return tuple(tuple(row) for row in matrix)


def matrix_of_word(word):
    """Matrix of ``x_1 ... x_k`` in the convention used by the pair checker."""

    matrix = base.identity_matrix()
    for root in reversed(word):
        matrix = base.left_elementary(matrix, *root)
    return matrix


def conjugate_by_root(matrix, root):
    """Return ``x matrix x``; every depth-one root is an involution in char 2."""

    matrix = base.left_elementary(matrix, *root)
    return base.right_elementary(matrix, *root)


def structurally_possible(matrix, root):
    """Necessary row/column-cross condition for the result to be constant."""

    source, target, _ = root
    source_column = base.INDEX[source]
    target_row = base.INDEX[target]
    for row_index, row in enumerate(matrix):
        for column_index, entry in enumerate(row):
            if (
                base.constant_bit(entry) is None
                and row_index != target_row
                and column_index != source_column
            ):
                return False
    return True


def signed_generator_survives(pair_conjugate, third, generator_index, character):
    """Check one exact signed-Hecke generator after adjoining ``third``."""

    if not structurally_possible(pair_conjugate, third):
        return False
    conjugate = conjugate_by_root(pair_conjugate, third)
    constant = base.to_constant_matrix(conjugate)
    return (
        constant is not None
        and constant in character
        and character[constant] == (generator_index < 3)
    )


def main() -> None:
    character = base.signed_l0()
    positions = tuple(
        (source, target)
        for source in base.COORDS
        for target in base.COORDS
        if source != target
    )
    roots = tuple(
        (source, target, base.canonical((coefficient,)))
        for source, target in positions
        for coefficient in base.COEFFICIENTS
    )
    outside = tuple(root for root in roots if not base.root_normalizes(root, character))
    assert len(roots) == 336
    assert len(outside) == 304

    # Reproduce the established two-letter result as an orientation and
    # normalizer-regression test before extending it.
    pair_returns = 0
    for first in outside:
        for second in outside:
            if base.pair_normalizes(first, second, character):
                pair_returns += 1
                assert base.pair_product_is_constant(first, second)
    assert pair_returns == 338

    # Products with equal exact matrices have identical conjugation behavior
    # against every third root, so retain one representative of each product.
    pair_products = {}
    for first in outside:
        for second in outside:
            key = matrix_key(matrix_of_word((first, second)))
            pair_products.setdefault(key, (first, second))
    assert len(pair_products) == 54_897

    # This order is only a speed optimization.  A candidate must survive every
    # signed generator, so changing the order cannot change the verdict.
    generator_order = (2, 3, 5, 0, 7, 8, 9, 1, 6, 4)
    stage_totals = [0] * (len(generator_order) + 1)
    hits = []

    for first, second in pair_products.values():
        candidates = outside
        for stage, generator_index in enumerate(generator_order, start=1):
            pair_conjugate = base.conjugate_generator(
                first, second, base.ARROWS[generator_index]
            )
            candidates = tuple(
                third
                for third in candidates
                if signed_generator_survives(
                    pair_conjugate, third, generator_index, character
                )
            )
            stage_totals[stage] += len(candidates)
            if not candidates:
                break
        for third in candidates:
            hits.append((first, second, third))

    # The eighth tested generator already kills the final 6,130 candidates;
    # the last two rows are retained in the code as a complete definition of
    # the signed normalizer test.
    assert stage_totals == [
        0,
        4_181_384,
        2_335_930,
        1_099_624,
        253_920,
        23_736,
        23_736,
        6_130,
        0,
        0,
        0,
    ]
    assert not hits

    print("depth-one nonconstant roots:", len(roots))
    print("individually outside signed normalizer:", len(outside))
    print("ordered triples represented:", len(outside) ** 3)
    print("distinct exact first-two-factor products:", len(pair_products))
    print("candidate totals after successive generators:", stage_totals[1:])
    print("genuine three-root signed-Hecke returns:", len(hits))


if __name__ == "__main__":
    main()
