"""Exhaust two-chart embeddings through a natural alternating overgroup.

Fix the exceptional isomorphism ``GL(4,2) ~= A8`` supplied by GAP and let the
resulting ``A8`` act on the first eight points of ``A_n``.  Every second
labeled chart in this geometry is obtained by conjugating this embedding by
an element of ``S_n``; allowing odd conjugators also includes the outer
automorphism of the labeled ``A8`` chart.  The supported degrees are 9 and
10, for which the generated group is ``A8``, ``A9``, or ``A10`` and hence
centerless.

An atlas kernel word is central exactly when its value is the identity.  The
scan therefore tests the actual centrality
relations without forming commutators.  It first applies all 234 radius-five
boundary words and then selected interior collision-tree words.

This is a finite falsification test, not a proof about arbitrary finite or
tracial models.  A survivor would nevertheless be an exact regular-margin
finite model: in the left regular representation of the generated finite
group, each embedded ``A8`` restricts as copies of its regular
representation.

Run under Sage, whose bundled GAP supplies the exceptional isomorphism.
"""

import argparse
from collections import Counter
import itertools
import json
import math
import time

from sage.all import AlternatingGroup, GF, GL, libgap

from atlas_certified_a8_alignment import boundary_words
from atlas_kernel_collision_enumerator import (
    enumerate_ball,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import factor_generators, gf2_mul


def multiply(left, right):
    """GAP/Sage right-action product of zero-based permutation tuples."""
    return tuple(right[left[index]] for index in range(len(left)))


def inverse(permutation):
    result = [0] * len(permutation)
    for source, target in enumerate(permutation):
        result[target] = source
    return tuple(result)


def conjugate(conjugator, element, conjugator_inverse):
    return multiply(multiply(conjugator, element), conjugator_inverse)


def gap_tuple(element, degree):
    return (tuple(int(value) - 1 for value in libgap.ListPerm(element, 8))
            + tuple(range(8, degree)))


def exceptional_a8_map(matrices, degree):
    source = GL(4, GF(2))
    target = AlternatingGroup(8)
    isomorphism = libgap.IsomorphismGroups(source, target)
    if isomorphism is libgap.fail:
        raise AssertionError("GAP did not construct GL(4,2) ~= A8")
    answer = {}
    for matrix in matrices:
        key = bytes(int(value) for value in matrix.reshape(-1))
        source_element = source(matrix.tolist())
        answer[key] = gap_tuple(isomorphism.Image(source_element._libgap_()), degree)
    return answer


def matrix_key(matrix):
    return bytes(int(value) for value in matrix.reshape(-1))


def collect_matrices(words):
    matrices = {}
    for word in words:
        for _factor, matrix in word:
            matrices[matrix_key(matrix)] = matrix
    for _name, word in factor_generators()[:6]:
        matrix = word[0][1]
        matrices[matrix_key(matrix)] = matrix
    return list(matrices.values())


def evaluate(word, images, conjugator, conjugator_inverse, cache, identity):
    value = identity
    for factor, matrix in word:
        image = images[matrix_key(matrix)]
        if factor == 2:
            key = image
            aligned = cache.get(key)
            if aligned is None:
                aligned = conjugate(conjugator, image, conjugator_inverse)
                cache[key] = aligned
            image = aligned
        value = multiply(value, image)
    return value


def moved_fixed_points(permutation):
    """Fixed points of the conjugated eight-point alternating subgroup."""
    conjugator_inverse = inverse(permutation)
    return sorted(conjugator_inverse[index] for index in range(8, len(permutation)))


def run(degree, interior_indices, max_seconds):
    if degree not in (9, 10):
        raise ValueError("the centerless generated-group check is certified for 9 and 10")
    identity = tuple(range(degree))
    boundary = boundary_words()
    states, sphere_sizes = enumerate_ball(5)
    collision_words, _, _ = spanning_tree_kernel_words(states)
    interior = [collision_words[index] for index in interior_indices]
    active_words = boundary + interior
    generators = [word[0][1] for _name, word in factor_generators()[:6]]
    matrices = collect_matrices(active_words)
    matrices.extend(gf2_mul(left, right)
                    for left in generators for right in generators)
    images = exceptional_a8_map(matrices, degree)

    # Verify the exceptional map on every adjacent generator product before
    # trusting the 9! scan.
    for left in generators:
        for right in generators:
            expected = images[matrix_key(gf2_mul(left, right))]
            observed = multiply(images[matrix_key(left)], images[matrix_key(right)])
            if observed != expected:
                raise AssertionError("exceptional A8 map is not multiplicative")

    started = time.monotonic()
    tested = 0
    boundary_survivors = []
    combined_survivors = []
    first_failure_histogram = Counter()
    timed_out = False

    fixed_point_count = degree - 8
    centralizer_order = math.factorial(fixed_point_count)
    for permutation in itertools.permutations(range(degree)):
        if time.monotonic() - started > max_seconds:
            timed_out = True
            break
        # Right multiplication by a permutation of the points fixed by the
        # base A8 does not change the conjugated labeled chart.  Keep the
        # unique representative in which their inverse images are ordered.
        fixed_preimages = [permutation.index(index) for index in range(8, degree)]
        if fixed_preimages != sorted(fixed_preimages):
            continue
        tested += 1
        conjugator = tuple(permutation)
        conjugator_inverse = inverse(conjugator)
        cache = {}
        failed = False
        for index, word in enumerate(boundary):
            if evaluate(word, images, conjugator, conjugator_inverse, cache, identity) != identity:
                first_failure_histogram[index] += 1
                failed = True
                break
        if failed:
            continue
        record = {
            "conjugator": [value + 1 for value in conjugator],
            "second_chart_fixed_points": [value + 1 for value in moved_fixed_points(conjugator)],
        }
        boundary_survivors.append(record)
        if all(evaluate(word, images, conjugator, conjugator_inverse, cache, identity) == identity
               for word in interior):
            combined_survivors.append(record)

    return {
        "overgroup": f"A{degree} natural eight-point-support geometry",
        "conjugators": (f"S{degree} modulo the pointwise-chart centralizer "
                         "(both label parities)"),
        "conjugators_expected": math.factorial(degree) // centralizer_order,
        "conjugators_tested": tested,
        "boundary_words": len(boundary),
        "interior_indices": interior_indices,
        "sphere_sizes": sphere_sizes,
        "boundary_survivor_count": len(boundary_survivors),
        "combined_survivor_count": len(combined_survivors),
        "boundary_survivors": boundary_survivors,
        "combined_survivors": combined_survivors,
        "first_boundary_failure_histogram": sorted(first_failure_histogram.items()),
        "timed_out": timed_out,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--degree", type=int, choices=(9, 10), default=9)
    parser.add_argument("--interior-indices", type=int, nargs="+", default=(19243,))
    parser.add_argument("--max-seconds", type=float, default=120.0)
    args = parser.parse_args()
    print(json.dumps(run(args.degree, args.interior_indices, args.max_seconds), indent=2))


if __name__ == "__main__":
    main()
