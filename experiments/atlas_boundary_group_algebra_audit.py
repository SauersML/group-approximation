"""Audit the classical-boundary Jacobian inside the group algebra of A8.

At the unique inner alignment every first-boundary word is the identity.
Its right-trivialized derivative is

    D_w(X) = sum_j (Ad(P_{j-1}) - Ad(P_j)) X,

where ``j`` runs through second-chart syllables.  The signed prefix sum is
an integral group-algebra element ``q_w``.  This script computes those
elements exactly in ``GL(4,2) ~= A8`` and first checks the strongest cheap
possibility: whether the two-support ``q_w`` already generate the rank-three
subgroup ``H = diag(GL(3,2),1)`` through their support ratios.

If they do, tangent H-rigidity follows by direct telescoping, without a
20,160-dimensional regular Jacobian.  The output also records all sparse
supports for subsequent right-ideal calculations.
"""

import argparse
import json
from collections import Counter, deque

import numpy as np

from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


def group_algebra_derivative(word, alignment, alignment_inverse):
    prefix = I4.copy()
    coefficients = Counter()
    for factor, matrix in word:
        image = matrix
        if factor == 2:
            image = gf2_mul(gf2_mul(
                alignment, matrix), alignment_inverse)
        before = prefix
        prefix = gf2_mul(prefix, image)
        if factor == 2:
            coefficients[matrix_key(before)] += 1
            coefficients[matrix_key(prefix)] -= 1
    if matrix_key(prefix) != matrix_key(I4):
        raise AssertionError("boundary word is nontrivial at alignment")
    return {key: coefficient for key, coefficient in coefficients.items()
            if coefficient}


def matrix_from_key(key):
    return np.frombuffer(key, dtype=np.uint8).reshape(4, 4).copy()


def two_support_ratio(coefficients):
    if len(coefficients) != 2:
        return None
    items = list(coefficients.items())
    if items[0][1] != -items[1][1]:
        return None
    # Right translation by a^{-1} turns c(a-b) into c(1-b a^{-1}).
    if items[0][1] > 0:
        a_key, coefficient = items[0]
        b_key, _ = items[1]
    else:
        a_key, coefficient = items[1]
        b_key, _ = items[0]
    a = matrix_from_key(a_key)
    b = matrix_from_key(b_key)
    return gf2_mul(b, gf2_inv(a)), coefficient


def generated_subgroup(generators):
    identity_key = matrix_key(I4)
    elements = {identity_key: I4.copy()}
    queue = deque([I4.copy()])
    generators_with_inverses = []
    for generator in generators:
        generators_with_inverses.extend((generator, gf2_inv(generator)))
    while queue:
        element = queue.popleft()
        for generator in generators_with_inverses:
            target = gf2_mul(element, generator)
            key = matrix_key(target)
            if key not in elements:
                elements[key] = target
                queue.append(target)
    return list(elements.values())


def lies_in_h(matrix):
    expected = I4.copy()
    expected[:3, :3] = matrix[:3, :3]
    return np.array_equal(matrix, expected)


def sparse_record(coefficients):
    return sorted((key.hex(), value) for key, value in coefficients.items())


def run(include_supports):
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    derivatives = [group_algebra_derivative(
        word, alignment, alignment_inverse) for word in boundary_words()]
    ratios = []
    ratio_records = []
    for index, derivative in enumerate(derivatives):
        result = two_support_ratio(derivative)
        if result is None:
            continue
        ratio, coefficient = result
        ratios.append(ratio)
        ratio_records.append({
            "boundary_index": index,
            "ratio_hex": matrix_key(ratio).hex(),
            "coefficient": coefficient,
            "ratio_in_h": lies_in_h(ratio),
        })
    h_ratios = [ratio for ratio in ratios if lies_in_h(ratio)]
    subgroup = generated_subgroup(h_ratios)
    result = {
        "boundary_relations": len(derivatives),
        "support_size_histogram": sorted(Counter(
            len(derivative) for derivative in derivatives).items()),
        "two_support_derivatives": len(ratios),
        "two_support_ratios_in_h": len(h_ratios),
        "subgroup_generated_by_h_ratios_order": len(subgroup),
        "subgroup_generated_by_h_ratios_is_h": (
            len(subgroup) == 168 and all(lies_in_h(g) for g in subgroup)),
        "ratio_records": ratio_records,
    }
    if include_supports:
        result["derivatives"] = [
            sparse_record(derivative) for derivative in derivatives]
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--include-supports", action="store_true")
    args = parser.parse_args()
    print(json.dumps(run(args.include_supports), indent=2))


if __name__ == "__main__":
    main()
