"""Search for a one-transverse-chart relation via subgroup intersection.

After the fixed classical alignment, a kernel word with exactly one
second-chart syllable outside the aligned rank-three subgroup exists exactly
when

    <A8_chart1, H_chart2> intersects A8_chart2 outside H_chart2.

This script searches that intersection directly.  Leavitt elements are
stored in a canonical sparse normal form for the direct system

    M_(2^(n+d),2^n)(F2) -> M_(2^(n+d+1),2^(n+1))(F2), x |-> x tensor I_2.

The normal form expands each gauge degree to a common right depth and then
removes every possible trailing tensor-I_2 factor.  Hits are replayed with
the independent exact Leavitt equality checker before being reported.
"""

import argparse
import json
import time

from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_kernel_collision_enumerator import (
    common_right_depths,
    enumerate_ball,
    exact_image_key,
)
from atlas_two_chart_search import (
    factor_generators,
    gf2_inv,
    gf2_mul,
    leavitt_chart_element,
    leavitt_is_one,
    leavitt_mul,
    matrix_key,
    transvection,
)


ONE = {((), ()): 1}


def canonical_degree(terms, degree):
    """Canonical sparse representative of one homogeneous gauge degree."""
    min_depth = max(0, -degree)
    depth = max((len(right) for _, right in terms), default=min_depth)
    expanded = set()
    for left, right in terms:
        extra = depth - len(right)
        for suffix_bits in range(1 << extra):
            suffix = tuple(
                (suffix_bits >> (extra - 1 - bit)) & 1
                for bit in range(extra)
            )
            monomial = (left + suffix, right + suffix)
            if monomial in expanded:
                expanded.remove(monomial)
            else:
                expanded.add(monomial)

    while depth > min_depth:
        parents = {}
        collapsible = True
        for left, right in expanded:
            if not left or not right or left[-1] != right[-1]:
                collapsible = False
                break
            parent = (left[:-1], right[:-1])
            parents.setdefault(parent, set()).add(left[-1])
        if not collapsible or any(bits != {0, 1} for bits in parents.values()):
            break
        expanded = set(parents)
        depth -= 1
    return depth, tuple(sorted(expanded))


def canonical_key(value):
    by_degree = {}
    for left, right in value:
        by_degree.setdefault(len(left) - len(right), []).append((left, right))
    records = [
        (degree,) + canonical_degree(terms, degree)
        for degree, terms in sorted(by_degree.items())
    ]
    return tuple(record for record in records if record[2])


def value_from_key(key):
    return {monomial: 1 for _degree, _depth, terms in key for monomial in terms}


def lies_in_h(matrix):
    return (
        all(matrix[3, col] == (1 if col == 3 else 0) for col in range(4))
        and all(matrix[row, 3] == (1 if row == 3 else 0) for row in range(4))
    )


def encoded_matrix(matrix):
    return matrix_key(matrix).hex()


def validate_normal_form(radius):
    """Compare canonical buckets with the independent fixed-depth buckets."""
    states, sphere_sizes = enumerate_ball(radius)
    depths = common_right_depths(states)
    reference_to_canonical = {}
    canonical_to_reference = {}
    first_by_reference = {}
    counterexample = None
    for word, value in states:
        reference = exact_image_key(value, depths)
        canonical = canonical_key(value)
        previous = first_by_reference.get(reference)
        if previous is None:
            first_by_reference[reference] = (canonical, word, value)
        elif counterexample is None and previous[0] != canonical:
            counterexample = {
                "first_word": [
                    {"factor": factor, "matrix_f2_hex": encoded_matrix(matrix)}
                    for factor, matrix in previous[1]
                ],
                "second_word": [
                    {"factor": factor, "matrix_f2_hex": encoded_matrix(matrix)}
                    for factor, matrix in word
                ],
                "first_canonical": repr(previous[0]),
                "second_canonical": repr(canonical),
                "first_value": repr(previous[2]),
                "second_value": repr(value),
            }
        reference_to_canonical.setdefault(reference, set()).add(canonical)
        canonical_to_reference.setdefault(canonical, set()).add(reference)
    return {
        "validation_radius": radius,
        "states": len(states),
        "sphere_sizes": sphere_sizes,
        "reference_image_count": len(reference_to_canonical),
        "canonical_image_count": len(canonical_to_reference),
        "max_canonical_keys_per_reference": max(
            map(len, reference_to_canonical.values()), default=0
        ),
        "max_reference_keys_per_canonical": max(
            map(len, canonical_to_reference.values()), default=0
        ),
        "partitions_agree": (
            all(len(values) == 1 for values in reference_to_canonical.values())
            and all(len(values) == 1 for values in canonical_to_reference.values())
        ),
        "first_counterexample": counterexample,
    }


def search(radius, max_states, max_seconds):
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)

    generators = []
    for name, word in factor_generators()[:6]:
        generators.append((name, 1, word[0][1]))
    for row, col in ((0, 1), (1, 0), (1, 2), (2, 1)):
        h = transvection(row, col)
        original = gf2_mul(gf2_mul(alignment_inverse, h), alignment)
        generators.append(("h2_%d%d" % (row, col), 2, original))

    target_by_key = {}
    h2_count = 0
    for matrix in enumerate_gl4():
        aligned = gf2_mul(gf2_mul(alignment, matrix), alignment_inverse)
        if lies_in_h(aligned):
            h2_count += 1
            continue
        key = canonical_key(leavitt_chart_element(2, matrix))
        target_by_key.setdefault(key, matrix)

    one_key = canonical_key(ONE)
    seen = {one_key}
    frontier = [(one_key, ())]
    sphere_sizes = [1]
    started = time.monotonic()

    for level in range(1, radius + 1):
        next_frontier = []
        for key, word in frontier:
            value = value_from_key(key)
            for generator_index, (_name, factor, matrix) in enumerate(generators):
                product_value = leavitt_mul(
                    value, leavitt_chart_element(factor, matrix)
                )
                product_key = canonical_key(product_value)
                if product_key in seen:
                    continue
                seen.add(product_key)
                product_word = word + (generator_index,)
                target = target_by_key.get(product_key)
                if target is not None:
                    replay = ONE
                    encoded_word = []
                    for index in product_word:
                        name, replay_factor, replay_matrix = generators[index]
                        replay = leavitt_mul(
                            replay,
                            leavitt_chart_element(replay_factor, replay_matrix),
                        )
                        encoded_word.append({
                            "name": name,
                            "factor": replay_factor,
                            "matrix_f2_hex": encoded_matrix(replay_matrix),
                        })
                    replay = leavitt_mul(
                        replay, leavitt_chart_element(2, gf2_inv(target))
                    )
                    if not leavitt_is_one(replay):
                        raise AssertionError("canonical-key hit failed exact replay")
                    return {
                        "status": "hit",
                        "radius": radius,
                        "hit_level": level,
                        "states": len(seen),
                        "sphere_sizes": sphere_sizes + [len(next_frontier) + 1],
                        "h2_elements": h2_count,
                        "transverse_target_hex": encoded_matrix(target),
                        "subgroup_word": encoded_word,
                        "elapsed_seconds": time.monotonic() - started,
                    }
                next_frontier.append((product_key, product_word))
                if len(seen) >= max_states:
                    return {
                        "status": "state_limit",
                        "radius": radius,
                        "completed_level": level - 1,
                        "states": len(seen),
                        "sphere_sizes": sphere_sizes,
                        "h2_elements": h2_count,
                        "elapsed_seconds": time.monotonic() - started,
                    }
                if time.monotonic() - started >= max_seconds:
                    return {
                        "status": "time_limit",
                        "radius": radius,
                        "completed_level": level - 1,
                        "states": len(seen),
                        "sphere_sizes": sphere_sizes,
                        "h2_elements": h2_count,
                        "elapsed_seconds": time.monotonic() - started,
                    }
        frontier = next_frontier
        sphere_sizes.append(len(frontier))
    return {
        "status": "no_hit",
        "radius": radius,
        "completed_level": radius,
        "states": len(seen),
        "sphere_sizes": sphere_sizes,
        "h2_elements": h2_count,
        "elapsed_seconds": time.monotonic() - started,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=6)
    parser.add_argument("--max-states", type=int, default=2_000_000)
    parser.add_argument("--max-seconds", type=float, default=90.0)
    parser.add_argument("--validate-radius", type=int)
    args = parser.parse_args()
    result = (
        validate_normal_form(args.validate_radius)
        if args.validate_radius is not None
        else search(args.radius, args.max_states, args.max_seconds)
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
