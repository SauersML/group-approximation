"""Certify the unique inner alignment that repairs the first atlas boundary.

The tensor-flip audit isolates 234 radius-five collision words with a
nontrivial factor projection.  This script exhausts GL(4,2) and tests the
classical identification

    h_1 -> h,    h_2 -> k h k^-1

on those words using exact arithmetic over F_2.  It also reports how many
words in the complete collision tree are killed by the unique solution.
"""

import json
import sys

sys.path.insert(0, "experiments")

from atlas_kernel_collision_enumerator import (  # noqa: E402
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import (  # noqa: E402
    I4,
    factor_generators,
    gf2_inv,
    gf2_mul,
    matrix_key,
)


def enumerate_gl4():
    """Enumerate GL(4,2) from the six standard transvections."""
    generators = [word[0][1] for _, word in factor_generators()[:6]]
    elements = [I4.copy()]
    seen = {matrix_key(I4)}
    for element in elements:
        for generator in generators:
            target = gf2_mul(element, generator)
            key = matrix_key(target)
            if key not in seen:
                seen.add(key)
                elements.append(target)
    if len(elements) != 20160:
        raise AssertionError("GL(4,2) enumeration failed")
    return elements


def aligned_value(word, alignment, alignment_inverse):
    """Evaluate a free-product word under an inner chart alignment."""
    value = I4.copy()
    for factor, matrix in word:
        image = matrix
        if factor == 2:
            image = gf2_mul(gf2_mul(
                alignment, matrix), alignment_inverse)
        value = gf2_mul(value, image)
    return matrix_key(value)


def main():
    states, sphere_sizes = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    identity_key = matrix_key(I4)
    boundary = [word for word in words if any(
        matrix_key(projection) != identity_key
        for projection in factor_projections(word))]
    if len(boundary) != 234:
        raise AssertionError("first boundary changed")

    solutions = []
    for alignment in enumerate_gl4():
        alignment_inverse = gf2_inv(alignment)
        if all(aligned_value(word, alignment, alignment_inverse)
               == identity_key for word in boundary):
            solutions.append(alignment)
    if len(solutions) != 1:
        raise AssertionError("boundary alignment is not unique")

    alignment = solutions[0]
    alignment_inverse = gf2_inv(alignment)
    killed_tree_words = sum(
        aligned_value(word, alignment, alignment_inverse) == identity_key
        for word in words)
    result = {
        "radius": 5,
        "sphere_sizes": sphere_sizes,
        "collision_tree_words": len(words),
        "boundary_words": len(boundary),
        "inner_alignments_tested": 20160,
        "boundary_solutions": len(solutions),
        "unique_alignment_f2_hex": matrix_key(alignment).hex(),
        "unique_alignment_order": 2,
        "boundary_words_killed": len(boundary),
        "collision_tree_words_killed": killed_tree_words,
        "collision_tree_words_not_killed": len(words) - killed_tree_words,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
