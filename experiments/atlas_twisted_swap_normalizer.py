"""Exhaust coordinate twists of the inner two-chart prefix swap.

Let K1 and K2 be the two GL(4,2) scalar charts used by the Leavitt atlas,
and let v be the prefix-replacement unit with v K1 v^-1 = K2 and
v K2 v^-1 = K1, preserving matrix coordinates.  Every two-sided coordinate
twist of v has the form

    w_M = M_2 v,  M in GL(4,2).

Such a twist still exchanges the two chart subgroups precisely when the
Leavitt unit M_2 normalizes K1.  This script exhausts all 20,160 choices and
tests membership in K1 exactly over F_2.  It also reports the induced action
on the four perfect-overlap survivor classes.
"""

import json
import sys

sys.path.insert(0, "experiments")

from atlas_boundary_inner_alignment import enumerate_gl4  # noqa: E402
from atlas_kernel_collision_enumerator import (  # noqa: E402
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_perfect_overlap_scan import cardinality_obstruction  # noqa: E402
from atlas_survivor_conjugacy import (  # noqa: E402
    cyclic_reduce,
    invert_word,
    unoriented_key,
)
from atlas_survivor_prefix_gallery import chart_matrix  # noqa: E402
from atlas_two_chart_search import (  # noqa: E402
    I4,
    factor_generators,
    gf2_inv,
    gf2_mul,
    leavitt_chart_element,
    leavitt_mul,
    matrix_key,
)


CHART_ONE = ("01", "1", "000", "001")


def chart_one_generators():
    """The six standard transvections, without relying on list order."""
    generators = []
    seen = set()
    for _name, word in factor_generators():
        factor, matrix = word[0]
        key = matrix_key(matrix)
        if factor == 1 and key not in seen:
            seen.add(key)
            generators.append(matrix)
    if len(generators) != 6:
        raise AssertionError("the standard GL(4,2) generating set changed")
    return generators


def conjugate_chart_one_coordinate(matrix, element):
    """Return the K1 coordinate of matrix_2 element_1 matrix_2^-1."""
    inverse = gf2_inv(matrix)
    value = leavitt_mul(
        leavitt_mul(
            leavitt_chart_element(2, matrix),
            leavitt_chart_element(1, element),
        ),
        leavitt_chart_element(2, inverse),
    )
    return chart_matrix(value, CHART_ONE)


def normalizer_elements():
    """Compute K2 intersect N_Q(K1) by an exact generator test."""
    generators = chart_one_generators()
    answer = []
    for matrix in enumerate_gl4():
        coordinates = {}
        for generator in generators:
            coordinate = conjugate_chart_one_coordinate(matrix, generator)
            if coordinate is None:
                break
            coordinates[matrix_key(generator)] = coordinate
        else:
            answer.append((matrix, coordinates))
    return answer


def survivor_classes():
    """Return the four freely cyclically reduced survivor representatives."""
    states, _sphere_sizes = enumerate_ball(5)
    words, _collision_sizes, _depths = spanning_tree_kernel_words(states)
    identity = matrix_key(I4)
    boundary = [
        word
        for word in words
        if any(
            matrix_key(projection) != identity
            for projection in factor_projections(word)
        )
    ]
    classes = {}
    for index, word in enumerate(boundary):
        obstruction = cardinality_obstruction(word)
        if obstruction["positive_cardinality_obstruction_rows"]:
            classes.setdefault(
                unoriented_key(word), (index, cyclic_reduce(word))
            )
    if [index for index, _word in classes.values()] != [11, 30, 44, 55]:
        raise AssertionError("survivor classification changed")
    return list(classes.values())


def encoded_word(word):
    return tuple((factor, matrix_key(matrix)) for factor, matrix in word)


def oriented_class(word, classes):
    """Identify a cyclic word with a representative, retaining orientation."""
    core = encoded_word(cyclic_reduce(word))
    for index, representative in classes:
        for orientation, candidate in (
            (1, representative),
            (-1, invert_word(representative)),
        ):
            encoded = encoded_word(candidate)
            for offset in range(len(encoded)):
                if core == encoded[offset:] + encoded[:offset]:
                    return index, orientation
    raise AssertionError("twisted swap left the four survivor classes")


def twisted_swap_word(word, matrix):
    """Apply conjugation by w_M=M_2 v to a free-product word."""
    inverse = gf2_inv(matrix)
    answer = []
    for factor, element in word:
        if factor == 1:
            answer.append(
                (2, gf2_mul(gf2_mul(matrix, element), inverse))
            )
        else:
            coordinate = conjugate_chart_one_coordinate(matrix, element)
            if coordinate is None:
                raise AssertionError("normalizer failed on a chart element")
            answer.append((1, coordinate))
    return answer


def main():
    normalizer = normalizer_elements()
    classes = survivor_classes()
    actions = []
    for matrix, _coordinates in normalizer:
        actions.append(
            {
                "matrix_f2_hex": matrix_key(matrix).hex(),
                "class_action": {
                    str(index): list(oriented_class(
                        twisted_swap_word(representative, matrix), classes
                    ))
                    for index, representative in classes
                },
            }
        )
    print(json.dumps({
        "chart_group_order": 20160,
        "normalizer_intersection_order": len(normalizer),
        "normalizer_elements": [
            matrix_key(matrix).hex() for matrix, _coordinates in normalizer
        ],
        "twisted_swap_actions": actions,
    }, indent=2))


if __name__ == "__main__":
    main()
