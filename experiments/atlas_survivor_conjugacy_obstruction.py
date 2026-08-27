"""Certify that every conjugate of each live atlas class misses one chart.

For a cyclically reduced word in a free product, every conjugate has reduced
form u c u^-1 with c a cyclic rotation.  The support equivalence relation of
c is contained in that of the full conjugate.  A one-sign cardinality
obstruction is monotone under adding support identifications.  It therefore
suffices to test the cyclic rotations of each survivor and its inverse.
"""

import json
import sys

sys.path.insert(0, "experiments")

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
from atlas_two_chart_search import I4, matrix_key  # noqa: E402


def rotations(word):
    return [word[offset:] + word[:offset] for offset in range(len(word))]


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    identity_key = matrix_key(I4)
    boundary = [word for word in words if any(
        matrix_key(projection) != identity_key
        for projection in factor_projections(word))]
    survivors = [word for word in boundary if
                 cardinality_obstruction(word)[
                     "positive_cardinality_obstruction_rows"]]

    classes = {}
    for word in survivors:
        classes.setdefault(unoriented_key(word), word)
    if len(classes) != 4:
        raise AssertionError("survivor conjugacy classification changed")

    rows = []
    for index, representative in enumerate(classes.values()):
        core = cyclic_reduce(representative)
        variants = rotations(core) + rotations(invert_word(core))
        obstruction_rows = [
            cardinality_obstruction(word)[
                "positive_cardinality_obstruction_rows"]
            for word in variants
        ]
        if any(rows != [0, 1] for rows in obstruction_rows):
            raise AssertionError("a conjugacy-core orientation escaped")
        rows.append({
            "class": index,
            "cyclically_reduced_length": len(core),
            "oriented_rotations_tested": len(variants),
            "obstruction_rows_for_every_rotation": [0, 1],
            "all_conjugates_obstructed_by_monotonicity": True,
        })

    print(json.dumps({
        "boundary_words": len(boundary),
        "survivor_words": len(survivors),
        "central_classes_up_to_sign": len(classes),
        "classes": rows,
    }, indent=2))


if __name__ == "__main__":
    main()
