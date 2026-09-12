"""Verify a finite properly-infinite raw-compressor atlas packet.

The four-leaf prefix equivalence scalarizes the rank-four raw swap and comb
compressor to two units ``r,u`` of the binary Leavitt algebra.  A hard
boundary pair recovers the cylinder projections ``p_11`` and ``p_001``.
This script verifies that

    a0 = u* p_11             = 11000 11*,
    a1 = u* p_001 r p_11     = 111 11*

have the same initial projection ``p_11`` and orthogonal range projections.
All arithmetic is exact over F_2.
"""

import json
import sys

sys.path.insert(0, "experiments")

from atlas_kernel_collision_enumerator import ONE  # noqa: E402
from atlas_survivor_infinite_projection import hard_pairs  # noqa: E402
from atlas_survivor_prefix_obstruction import (  # noqa: E402
    cylinder_projection,
    leavitt_is_zero,
    leavitt_star,
    monomial_pool,
    span_certificates,
    verify_projection_identities,
)
from atlas_two_chart_search import leavitt_add, leavitt_mul  # noqa: E402


ZERO = {}
FOUR_LEAVES = ((0, 0), (0, 1), (1, 0), (1, 1))
GENERATOR_NAMES = ("q", "l", "q*", "l*")


def s(bit):
    return {((bit,), ()): 1}


def t(bit):
    return {((), (bit,)): 1}


def product(*values):
    result = ONE
    for value in values:
        result = leavitt_mul(result, value)
    return result


def scalarize(matrix):
    """Apply the full-depth-two prefix equivalence M_4(R) -> R."""
    result = ZERO
    for row in range(4):
        for column in range(4):
            entry = matrix[row][column]
            if not entry:
                continue
            term = product(
                {(FOUR_LEAVES[row], ()): 1},
                entry,
                {((), FOUR_LEAVES[column]): 1},
            )
            result = leavitt_add(result, term)
    return result


def raw_and_comb():
    p0 = product(s(0), t(0))
    p1 = product(s(1), t(1))
    raw = scalarize([
        [p0, ZERO, ZERO, s(1)],
        [ZERO, ONE, ZERO, ZERO],
        [ZERO, ZERO, ONE, ZERO],
        [t(1), ZERO, ZERO, ZERO],
    ])
    comb = scalarize([
        [s(0), ZERO, ZERO, p1],
        [ZERO, s(0), ZERO, product(p1, t(0))],
        [ZERO, ZERO, s(0), product(p1, t(0), t(0))],
        [ZERO, ZERO, ZERO, product(t(0), t(0), t(0))],
    ])
    return raw, comb


def assert_equal(left, right, message):
    if not leavitt_is_zero(leavitt_add(left, right)):
        raise AssertionError(message)


def word_string(word):
    if not word:
        return "1"
    return " ".join(GENERATOR_NAMES[index] for index in word)


def projection_certificates():
    """Recover p_11 and p_001 from the first hard pair."""
    _, _, _, _, q, letter = hard_pairs()[0]
    generators = (q, letter, leavitt_star(q), leavitt_star(letter))
    targets = [cylinder_projection("11"), cylinder_projection("001")]
    pool = monomial_pool(generators, 6)
    certificates, ambient_dimension, generated_rank = span_certificates(
        pool, targets)
    verify_projection_identities(generators, certificates, targets)
    return {
        "hard_pair": "class 11, forward rotation 0",
        "maximum_word_depth": 6,
        "ambient_expansion_terms": ambient_dimension,
        "generated_span_rank": generated_rank,
        "p_11": [word_string(word) for word in certificates[0]],
        "p_001": [word_string(word) for word in certificates[1]],
    }


def monomial_string(value):
    if len(value) != 1:
        raise AssertionError("expected one reduced monomial")
    (left, right), coefficient = next(iter(value.items()))
    if coefficient != 1:
        raise AssertionError("unexpected coefficient")
    return "%s %s*" % (
        "".join(map(str, left)) or "1",
        "".join(map(str, right)) or "1",
    )


def main():
    raw, comb = raw_and_comb()
    e = cylinder_projection("11")
    middle = cylinder_projection("001")

    a0 = product(leavitt_star(comb), e)
    a1 = product(leavitt_star(comb), middle, raw, e)
    f0 = cylinder_projection("11000")
    f1 = cylinder_projection("111")

    assert_equal(product(leavitt_star(a0), a0), e, "a0* a0 != e")
    assert_equal(product(a0, leavitt_star(a0)), f0, "a0 a0* != f0")
    assert_equal(product(leavitt_star(a1), a1), e, "a1* a1 != e")
    assert_equal(product(a1, leavitt_star(a1)), f1, "a1 a1* != f1")
    if product(f0, f1) or product(f1, f0):
        raise AssertionError("the two range projections are not orthogonal")

    print(json.dumps({
        "four_leaf_code": ["00", "01", "10", "11"],
        "raw_scalar_terms": sorted(monomial_string({term: 1}) for term in raw),
        "comb_scalar_terms": sorted(monomial_string({term: 1}) for term in comb),
        "projection_certificates": projection_certificates(),
        "partial_isometries": {
            "a0_formula": "u* p_11",
            "a0_reduced": monomial_string(a0),
            "a1_formula": "u* p_001 r p_11",
            "a1_reduced": monomial_string(a1),
        },
        "verified_identities": [
            "a0* a0 = p_11",
            "a0 a0* = p_11000",
            "a1* a1 = p_11",
            "a1 a1* = p_111",
            "p_11000 p_111 = p_111 p_11000 = 0",
        ],
        "properly_infinite_projection": "p_11",
    }, indent=2))


if __name__ == "__main__":
    main()
