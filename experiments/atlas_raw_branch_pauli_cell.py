"""Audit the exact raw/cylinder Pauli cells and the first hard escape.

The calculation uses all-depth exact arithmetic in the binary Leavitt
algebra over F_2.  It records both the useful finite Clifford structure and
the trace-balanced reason it does not yet imply a finite-trace contradiction.
"""

import collections
import json
import sys

sys.path.insert(0, "experiments")

from atlas_raw_compressed_heisenberg import (  # noqa: E402
    element_order,
    generated_subgroup,
    matrix_identity,
    order_histogram,
)
from atlas_raw_compressor_proper_infinite import (  # noqa: E402
    product,
    raw_and_comb,
    s,
    scalarize,
    t,
)
from atlas_survivor_infinite_projection import hard_pairs  # noqa: E402
from atlas_survivor_prefix_obstruction import (  # noqa: E402
    cylinder_projection,
    leavitt_is_zero,
)
from atlas_two_chart_search import leavitt_add  # noqa: E402


def equal(left, right):
    return leavitt_is_zero(leavitt_add(left, right))


def root(coefficient, row=0, column=2):
    value = matrix_identity()
    value[row][column] = coefficient
    return scalarize(value)


def inverse(value):
    order = element_order(value, 128)
    if order is None:
        raise AssertionError("finite-order inverse unavailable")
    return product(*([value] * (order - 1)))


def intersection_size(left, right):
    return sum(1 for value in left
               if any(equal(value, other) for other in right))


def conjugate_subgroup(value, subgroup):
    value_inverse = inverse(value)
    return [product(value, member, value_inverse) for member in subgroup]


def main():
    raw, _ = raw_and_comb()
    p0 = product(s(0), t(0))
    p1 = product(s(1), t(1))
    x0 = root(p0, 0, 1)
    y0 = root(p0, 1, 2)
    z0 = root(p0)
    z1 = root(p1)
    z11 = root(cylinder_projection("11"))
    z001 = root(cylinder_projection("001"))

    compressed_heisenberg = generated_subgroup((x0, y0), limit=16)
    complementary_pauli = generated_subgroup((raw, z1), limit=16)
    two_pauli_cell = generated_subgroup((x0, y0, raw, z1), limit=128)
    hard_projection_cell = generated_subgroup((raw, z11, z001), limit=32)

    c1 = product(raw, z1, raw, z1)
    c11 = product(raw, z11, raw, z11)

    q, ell = hard_pairs()[0][4:6]
    q_conjugate = conjugate_subgroup(q, two_pauli_cell)
    ell_conjugate = conjugate_subgroup(ell, two_pauli_cell)

    result = {
        "compressed_heisenberg": {
            "order": len(compressed_heisenberg),
            "order_histogram": order_histogram(compressed_heisenberg),
            "central_commutator_is_z0": equal(
                product(x0, y0, x0, y0), z0),
        },
        "complementary_raw_pauli": {
            "order": len(complementary_pauli),
            "order_histogram": order_histogram(complementary_pauli),
            "central_commutator_order": element_order(c1),
        },
        "two_pauli_cell": {
            "order": len(two_pauli_cell),
            "order_histogram": order_histogram(two_pauli_cell),
            "is_D8_times_D8_by_order_and_commuting_factors":
                len(two_pauli_cell) == 64
                and intersection_size(compressed_heisenberg,
                                      complementary_pauli) == 1
                and all(equal(product(left, right), product(right, left))
                        for left in compressed_heisenberg
                        for right in complementary_pauli),
        },
        "hard_projection_cell": {
            "generators": ["raw", "x_13(p_11)", "x_13(p_001)"],
            "order": len(hard_projection_cell),
            "order_histogram": order_histogram(hard_projection_cell),
            "raw_commutes_z001": equal(product(raw, z001),
                                        product(z001, raw)),
            "raw_commutes_z11": equal(product(raw, z11),
                                       product(z11, raw)),
            "raw_z11_commutator_order": element_order(c11),
            "structure": "D8 times C2",
            "regular_trace_c11_minus_z001_minus": "1/4",
            "regular_trace_add_z11_minus": "1/8",
            "raw_flips_z11_sign_on_c11_minus": True,
            "two_raw_arrows_fill_trace_quarter_carrier": True,
            "no_parent_trace_contradiction": "2*(1/8)=1/4",
        },
        "first_hard_escape": {
            "q_order": element_order(q),
            "ell_order": element_order(ell),
            "cell_intersection_q_cell_q_inverse":
                intersection_size(two_pauli_cell, q_conjugate),
            "cell_intersection_ell_cell_ell_inverse":
                intersection_size(two_pauli_cell, ell_conjugate),
        },
        "remaining_gate":
            "convert ring child-under-parent multiplication into spectral support containment",
    }
    expected = {
        "compressed_heisenberg": {
            "order": 8,
            "order_histogram": {1: 1, 2: 5, 4: 2},
            "central_commutator_is_z0": True,
        },
        "complementary_raw_pauli": {
            "order": 8,
            "order_histogram": {1: 1, 2: 5, 4: 2},
            "central_commutator_order": 2,
        },
        "two_pauli_cell": {
            "order": 64,
            "order_histogram": {1: 1, 2: 35, 4: 28},
            "is_D8_times_D8_by_order_and_commuting_factors": True,
        },
        "hard_projection_cell": {
            "generators": ["raw", "x_13(p_11)", "x_13(p_001)"],
            "order": 16,
            "order_histogram": {1: 1, 2: 11, 4: 4},
            "raw_commutes_z001": True,
            "raw_commutes_z11": False,
            "raw_z11_commutator_order": 2,
            "structure": "D8 times C2",
            "regular_trace_c11_minus_z001_minus": "1/4",
            "regular_trace_add_z11_minus": "1/8",
            "raw_flips_z11_sign_on_c11_minus": True,
            "two_raw_arrows_fill_trace_quarter_carrier": True,
            "no_parent_trace_contradiction": "2*(1/8)=1/4",
        },
        "first_hard_escape": {
            "q_order": 4,
            "ell_order": 2,
            "cell_intersection_q_cell_q_inverse": 1,
            "cell_intersection_ell_cell_ell_inverse": 2,
        },
        "remaining_gate":
            "convert ring child-under-parent multiplication into spectral support containment",
    }
    if result != expected:
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
