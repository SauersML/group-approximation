"""Enumerate complete finite-radius kernel windows for the two-chart atlas.

For the concrete epimorphism

    A8 * A8 -> L_F2(1,2)^times,

every kernel word of length at most 2r is a difference u v^-1 between two
words of length at most r having the same Leavitt image.  This script hashes
those images exactly and retains one spanning tree in every collision bucket.

The output is a mathematical enumeration artifact, not a numerical optimizer.
It uses the exact F2/prefix arithmetic from atlas_two_chart_search.py.
"""

import argparse
import itertools
import json

import numpy as np

from atlas_two_chart_search import (
    I4,
    commutator,
    factor_generators,
    gf2_inv,
    gf2_mul,
    inverse,
    leavitt_chart_element,
    leavitt_is_one,
    leavitt_mul,
    matrix_key,
    product,
)


ONE = {((), ()): 1}


def free_product_key(word):
    return tuple((factor, matrix_key(matrix)) for factor, matrix in word)


def evaluate_word(word):
    value = ONE
    for factor, matrix in word:
        value = leavitt_mul(value, leavitt_chart_element(factor, matrix))
    return value


def enumerate_ball(radius):
    """Return one shortest word and its exact image for every P-ball point."""
    generators = [word for _, word in factor_generators()]
    identity_key = free_product_key([])
    states = {identity_key: ([], ONE)}
    frontier = [identity_key]
    level_sizes = [1]
    for _ in range(radius):
        next_frontier = []
        for state_key in frontier:
            word, value = states[state_key]
            for generator in generators:
                new_word = product(word, generator)
                new_key = free_product_key(new_word)
                if new_key in states:
                    continue
                factor, matrix = generator[0]
                new_value = leavitt_mul(
                    value, leavitt_chart_element(factor, matrix)
                )
                states[new_key] = (new_word, new_value)
                next_frontier.append(new_key)
        frontier = next_frontier
        level_sizes.append(len(frontier))
    return list(states.values()), level_sizes


def common_right_depths(states):
    depths = {}
    for _, value in states:
        for left, right in value:
            degree = len(left) - len(right)
            depths[degree] = max(depths.get(degree, 0), len(right))
    return depths


def exact_image_key(value, depths):
    """Hash a Leavitt element after exact homogeneous prefix refinement.

    At a fixed gauge degree, monomials with a common right depth are matrix
    units and hence linearly independent.  Refining every value in the pool
    to the same depth therefore gives an exact, collision-free key.
    """
    expanded_by_degree = {}
    for left, right in value:
        degree = len(left) - len(right)
        extra = depths[degree] - len(right)
        expanded = expanded_by_degree.setdefault(degree, set())
        for suffix in itertools.product((0, 1), repeat=extra):
            monomial = (left + suffix, right + suffix)
            if monomial in expanded:
                expanded.remove(monomial)
            else:
                expanded.add(monomial)
    return tuple(
        (degree, tuple(sorted(terms)))
        for degree, terms in sorted(expanded_by_degree.items())
        if terms
    )


def spanning_tree_kernel_words(states):
    depths = common_right_depths(states)
    buckets = {}
    for word, value in states:
        buckets.setdefault(exact_image_key(value, depths), []).append(word)

    kernel_words = []
    kernel_word_keys = set()
    collision_sizes = []
    for words in buckets.values():
        if len(words) < 2:
            continue
        collision_sizes.append(len(words))
        anchor = words[0]
        for word in words[1:]:
            difference = product(word, inverse(anchor))
            if difference:
                if not leavitt_is_one(evaluate_word(difference)):
                    raise AssertionError("exact image bucket produced a non-kernel word")
                difference_key = free_product_key(difference)
                if difference_key not in kernel_word_keys:
                    kernel_word_keys.add(difference_key)
                    kernel_words.append(difference)
    return kernel_words, collision_sizes, depths


def centrality_constraints(kernel_words):
    constraints = []
    keys = set()
    for _, generator in factor_generators():
        for kernel_word in kernel_words:
            word = commutator(generator, kernel_word)
            key = free_product_key(word)
            if word and key not in keys:
                keys.add(key)
                constraints.append(word)
    return constraints


def factor_projections(word):
    projections = []
    for selected_factor in (1, 2):
        value = I4.copy()
        for factor, matrix in word:
            if factor == selected_factor:
                value = gf2_mul(value, matrix)
        projections.append(value)
    return tuple(projections)


def lies_in_rank_three_subgroup(matrix):
    """Test membership in diag(GL(3,F2),1) inside GL(4,F2)."""
    return (
        np.array_equal(matrix[3, :], np.array((0, 0, 0, 1), dtype=np.uint8))
        and np.array_equal(
            matrix[:, 3], np.array((0, 0, 0, 1), dtype=np.uint8))
    )


def maximal_stabilizer_boundary_audit(kernel_words):
    """Audit the 15 point and 15 hyperplane stabilizers of GL(4,F2)."""
    selected_generators = [word[0][1]
                           for _name, word in factor_generators()[:6]]

    def matrix_commutator(left, right):
        return gf2_mul(
            gf2_mul(gf2_mul(left, right), gf2_inv(left)), gf2_inv(right))

    boundary = []
    for word in kernel_words:
        projections = factor_projections(word)
        if any(matrix_key(value) != matrix_key(I4) for value in projections):
            boundary.append((word, projections))

    audits = []
    for kind in ("point", "hyperplane"):
        for bits in range(1, 16):
            vector = np.array(
                [(bits >> index) & 1 for index in range(4)], dtype=np.uint8)

            def inside(matrix):
                image = ((matrix @ vector) & 1 if kind == "point"
                         else (vector @ matrix) & 1)
                return np.array_equal(image, vector)

            contained = 0
            exposed = 0
            for word, projections in boundary:
                if not all(inside(matrix) for _factor, matrix in word):
                    continue
                contained += 1
                for projection in projections:
                    if matrix_key(projection) == matrix_key(I4):
                        continue
                    if any(
                        inside(generator)
                        and matrix_key(matrix_commutator(
                            generator, projection)) != matrix_key(I4)
                        for generator in selected_generators
                    ):
                        exposed += 1
                        break
            audits.append({
                "kind": kind,
                "fixed_vector_bits": bits,
                "contained_boundary_words": contained,
                "rigid_exposed_words": exposed,
            })
    return audits


def encode_word(word):
    return [
        {"factor": factor, "matrix_f2_hex": matrix_key(matrix).hex()}
        for factor, matrix in word
    ]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=3)
    parser.add_argument("--output", type=str)
    parser.add_argument("--deduplicate-constraints", action="store_true")
    args = parser.parse_args()
    if args.radius < 0:
        raise ValueError("radius must be nonnegative")

    states, level_sizes = enumerate_ball(args.radius)
    kernel_words, collision_sizes, depths = spanning_tree_kernel_words(states)
    constraints = (centrality_constraints(kernel_words)
                   if args.deduplicate_constraints else None)
    projection_counts = {}
    projection_pair_counts = {}
    boundary_support_counts = {}
    for word in kernel_words:
        projections = factor_projections(word)
        pattern = tuple(
            matrix_key(value) == matrix_key(I4) for value in projections
        )
        label = "%s,%s" % tuple(
            "identity" if entry else "nonidentity" for entry in pattern
        )
        projection_counts[label] = projection_counts.get(label, 0) + 1
        pair_label = ",".join(matrix_key(value).hex() for value in projections)
        projection_pair_counts[pair_label] = projection_pair_counts.get(pair_label, 0) + 1
        if not all(matrix_key(value) == matrix_key(I4)
                   for value in projections):
            support_label = ",".join((
                "factor1_all_H=%s" % all(
                    lies_in_rank_three_subgroup(matrix)
                    for factor, matrix in word if factor == 1),
                "factor2_all_H=%s" % all(
                    lies_in_rank_three_subgroup(matrix)
                    for factor, matrix in word if factor == 2),
                "p1_identity=%s" % (
                    matrix_key(projections[0]) == matrix_key(I4)),
                "p2_identity=%s" % (
                    matrix_key(projections[1]) == matrix_key(I4)),
            ))
            boundary_support_counts[support_label] = (
                boundary_support_counts.get(support_label, 0) + 1)
    summary = {
        "radius": args.radius,
        "complete_kernel_word_radius": 2 * args.radius,
        "ball_size": len(states),
        "sphere_sizes": level_sizes,
        "image_count": len(states) - sum(size - 1 for size in collision_sizes),
        "collision_bucket_count": len(collision_sizes),
        "largest_collision_bucket": max(collision_sizes, default=1),
        "spanning_tree_kernel_generators": len(kernel_words),
        "factor_projection_patterns": dict(sorted(projection_counts.items())),
        "distinct_factor_projection_pairs": len(projection_pair_counts),
        "nontrivial_factor_projection_pairs": sum(
            1 for label in projection_pair_counts
            if label != "%s,%s" % (matrix_key(I4).hex(), matrix_key(I4).hex())
        ),
        "nontrivial_factor_projection_pair_counts": {
            label: count
            for label, count in sorted(projection_pair_counts.items())
            if label != "%s,%s" % (
                matrix_key(I4).hex(), matrix_key(I4).hex())
        },
        "tensor_flip_boundary_H_support_strata": dict(
            sorted(boundary_support_counts.items())),
        "tensor_flip_boundary_maximal_stabilizer_audit": (
            maximal_stabilizer_boundary_audit(kernel_words)),
        "tensor_flip_unsatisfied_kernel_generators": sum(
            count for label, count in projection_counts.items()
            if label != "identity,identity"
        ),
        "commutator_constraints_upper_bound": 12 * len(kernel_words),
        "common_right_depth_by_degree": {
            str(degree): depth for degree, depth in sorted(depths.items())
        },
    }
    if constraints is not None:
        summary["distinct_commutator_constraints"] = len(constraints)
    print(json.dumps(summary, sort_keys=True))

    if args.output:
        artifact = {
            "summary": summary,
            "kernel_generators": [encode_word(word) for word in kernel_words],
        }
        with open(args.output, "w", encoding="utf-8") as handle:
            json.dump(artifact, handle, sort_keys=True, indent=2)
            handle.write("\n")


if __name__ == "__main__":
    main()
