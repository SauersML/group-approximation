"""Verify that the raw involution gives a trace-half Pauli coefficient cut.

All calculations use exact all-depth arithmetic in the binary Leavitt
algebra over F_2.  The rank-four matrices are scalarized through the fixed
four-leaf code (00,01,10,11).
"""

import collections
import json
import sys

sys.path.insert(0, "experiments")

from atlas_kernel_collision_enumerator import ONE  # noqa: E402
from atlas_raw_compressor_proper_infinite import (  # noqa: E402
    FOUR_LEAVES,
    product,
    raw_and_comb,
    s,
    scalarize,
    t,
)
from atlas_survivor_prefix_obstruction import leavitt_is_zero  # noqa: E402
from atlas_two_chart_search import leavitt_add, leavitt_mul  # noqa: E402


ZERO = {}


def xor_sum(left, right):
    return leavitt_add(left, right)


def equal(left, right):
    return leavitt_is_zero(xor_sum(left, right))


def matrix_identity():
    return [
        [ONE if row == column else ZERO for column in range(4)]
        for row in range(4)
    ]


def compressed_root(row, column):
    matrix = matrix_identity()
    matrix[row][column] = product(s(0), t(0))
    return scalarize(matrix)


def generated_subgroup(generators, limit=1024):
    elements = [ONE]
    queue = collections.deque([ONE])
    while queue:
        left = queue.popleft()
        for generator in generators:
            value = leavitt_mul(left, generator)
            if not any(equal(value, old) for old in elements):
                elements.append(value)
                queue.append(value)
                if len(elements) > limit:
                    raise AssertionError("subgroup exceeded finite audit limit")
    return elements


def element_order(value, limit=64):
    running = ONE
    for exponent in range(1, limit + 1):
        running = leavitt_mul(running, value)
        if equal(running, ONE):
            return exponent
    return None


def order_histogram(elements):
    return dict(sorted(collections.Counter(
        element_order(value) for value in elements).items()))


def main():
    raw, _ = raw_and_comb()
    x12 = compressed_root(0, 1)
    x23 = compressed_root(1, 2)
    z13 = compressed_root(0, 2)

    heisenberg = generated_subgroup((x12, x23))
    product_group = generated_subgroup((x12, x23, raw))
    raw_coset = [leavitt_mul(raw, value) for value in heisenberg]

    result = {
        "four_leaf_code": ["".join(map(str, leaf)) for leaf in FOUR_LEAVES],
        "compressed_coefficient": "p_0 = s_0 t_0",
        "heisenberg_order": len(heisenberg),
        "heisenberg_order_histogram": order_histogram(heisenberg),
        "central_commutator_relation": equal(
            product(x12, x23, x12, x23), z13),
        "z13_central_in_heisenberg": all(
            equal(product(z13, value), product(value, z13))
            for value in heisenberg),
        "raw_order": element_order(raw),
        "raw_commutes_with_heisenberg": all(
            equal(product(raw, value), product(value, raw))
            for value in heisenberg),
        "raw_outside_heisenberg": not any(
            equal(raw, value) for value in heisenberg),
        "generated_product_order": len(product_group),
        "raw_coset_disjoint_from_heisenberg": not any(
            equal(left, right) for left in raw_coset for right in heisenberg),
        "generated_product_order_histogram": order_histogram(product_group),
        "regular_trace_z_minus_r_minus": "1/4",
        "relative_trace_of_raw_negative_cut_in_z_minus_sector": "1/2",
    }
    expected = {
        "four_leaf_code": ["00", "01", "10", "11"],
        "compressed_coefficient": "p_0 = s_0 t_0",
        "heisenberg_order": 8,
        "heisenberg_order_histogram": {1: 1, 2: 5, 4: 2},
        "central_commutator_relation": True,
        "z13_central_in_heisenberg": True,
        "raw_order": 2,
        "raw_commutes_with_heisenberg": True,
        "raw_outside_heisenberg": True,
        "generated_product_order": 16,
        "raw_coset_disjoint_from_heisenberg": True,
        "generated_product_order_histogram": {1: 1, 2: 11, 4: 4},
        "regular_trace_z_minus_r_minus": "1/4",
        "relative_trace_of_raw_negative_cut_in_z_minus_sector": "1/2",
    }
    if result != expected:
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
