"""Exact <=180-element corner calculation; run on MSI, never locally.

Matrices are tuples of four binary columns. Group-algebra coefficients and
polynomials are bitsets. The corner unit is e, not the ambient identity.
"""

import argparse
import json
import time
from fractions import Fraction
from pathlib import Path


def bits(value):
    while value:
        bit = value & -value
        yield bit.bit_length() - 1
        value ^= bit


def matrix_product(left, right):
    columns = []
    for column in right:
        out = 0
        for j in bits(column):
            out ^= left[j]
        columns.append(out)
    return tuple(columns)


def field_product(left, right):
    """F_4=F_2[w]/(w^2+w+1), in the basis 1,w."""
    out = 0
    while right:
        if right & 1:
            out ^= left
        left <<= 1
        if left & 4:
            left ^= 7
        right >>= 1
    return out


def polynomial_divmod(left, right):
    assert right
    quotient = 0
    while left and left.bit_length() >= right.bit_length():
        shift = left.bit_length() - right.bit_length()
        quotient ^= 1 << shift
        left ^= right << shift
    return quotient, left


def polynomial_product(left, right):
    out = 0
    for j in bits(right):
        out ^= left << j
    return out


def polynomial_inverse(value, modulus):
    old_r, r, old_s, s = modulus, value, 0, 1
    while r:
        quotient, remainder = polynomial_divmod(old_r, r)
        old_r, r = r, remainder
        old_s, s = s, old_s ^ polynomial_product(quotient, s)
    assert old_r == 1
    return polynomial_divmod(old_s, modulus)[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    start = time.monotonic()
    identity = (1, 2, 4, 8)
    # G=[[0,1],[1,1]]. Ordered leaves: 000,001,010,011.
    parent = (4, 8, 5, 10)  # G tensor I_2
    child = (2, 3, 4, 8)  # diag(G,I_2)
    scalar = (2, 3, 8, 12)  # I_2 tensor G, the F_4 scalar action
    generators = [parent, child]
    assert all(matrix_product(g, scalar) == matrix_product(scalar, g)
               for g in generators)
    assert all(matrix_product(matrix_product(g, g), g) == identity
               for g in generators)
    elements = [identity]
    index = {identity: 0}
    for element in elements:
        for generator in generators:
            product = matrix_product(element, generator)
            if product not in index:
                index[product] = len(elements)
                elements.append(product)
                assert len(elements) <= 180
    table = [[index[matrix_product(g, h)] for h in elements]
             for g in elements]

    def multiply(left, right):
        out = 0
        right_support = list(bits(right))
        for i in bits(left):
            row = table[i]
            for j in right_support:
                out ^= 1 << row[j]
        return out

    def basis(g):
        return 1 << index[g]

    e = basis(child) ^ basis(matrix_product(child, child))
    parent_e = basis(parent) ^ basis(matrix_product(parent, parent))
    target = multiply(multiply(e, parent_e), e)
    assert multiply(e, e) == e
    assert multiply(e, target) == multiply(target, e) == target
    powers = []
    echelon = {}
    power = e
    for degree in range(len(elements) + 1):
        powers.append(power)
        residual, polynomial = power, 1 << degree
        while residual:
            pivot = residual.bit_length() - 1
            if pivot not in echelon:
                echelon[pivot] = (residual, polynomial)
                break
            old_vector, old_polynomial = echelon[pivot]
            residual ^= old_vector
            polynomial ^= old_polynomial
        if residual == 0:
            minimal = polynomial
            break
        power = multiply(power, target)
    else:
        raise AssertionError("finite-dimensional Krylov bound failed")

    def evaluate_polynomial(polynomial):
        out = 0
        for j in bits(polynomial):
            out ^= powers[j]
        return out

    nilpotent_index = (minimal & -minimal).bit_length() - 1
    regular_factor = minimal >> nilpotent_index
    assert nilpotent_index > 0 and regular_factor != 1
    # CRT: h=0 mod x^k, h=1 mod r; v=0 mod x^k, x*v=1 mod r.
    h_polynomial = polynomial_inverse(1 << nilpotent_index,
                                      regular_factor) << nilpotent_index
    v_polynomial = polynomial_inverse(1 << (nilpotent_index + 1),
                                      regular_factor) << nilpotent_index
    h = evaluate_polynomial(h_polynomial)
    v = evaluate_polynomial(v_polynomial)
    f = e ^ h
    assert evaluate_polynomial(minimal) == 0
    assert multiply(h, h) == h
    assert multiply(f, f) == f and f
    assert multiply(h, f) == multiply(f, h) == 0
    assert multiply(target, v) == multiply(v, target) == h
    assert multiply(multiply(h, v), h) == v
    assert multiply(f, powers[nilpotent_index]) == 0
    assert multiply(f, powers[nilpotent_index - 1]) != 0

    def natural(value):
        out = [0] * 4
        for i in bits(value):
            for j, column in enumerate(elements[i]):
                out[j] ^= column
        return out

    assert natural(e) == natural(target) == natural(h) == natural(v)
    assert natural(e) == [1, 2, 0, 0]
    assert natural(f) == [0, 0, 0, 0]

    # After conjugating the original f by u, it and the complementary
    # projector P both live in this same finite group. This compares the
    # concrete projective modules that the remaining full-group step needs.
    opposite = multiply(multiply(parent_e, e), parent_e)
    opposite_square = multiply(opposite, opposite)
    projector = parent_e ^ multiply(opposite_square, opposite_square)
    assert multiply(projector, projector) == projector
    assert natural(projector) == [0, 0, 4, 8]

    def regular_rank(value):
        echelon = {}
        for j in range(len(elements)):
            column = multiply(value, 1 << j)
            while column:
                pivot = column.bit_length() - 1
                if pivot not in echelon:
                    echelon[pivot] = column
                    break
                column ^= echelon[pivot]
        return len(echelon)

    ranks = {name: regular_rank(value) for name, value in (
        ("e", e), ("h", h), ("f_plus", f), ("P", projector))}
    assert ranks["e"] == ranks["h"] + ranks["f_plus"]
    assert ranks["f_plus"] == ranks["P"] > 0

    # Explicit center-trivial Steinberg block, not a search for a common
    # summand. The SL_2(F_4) factor has 20 order-three and 24 order-five
    # elements. Its integral character projector reduces to their sum.
    special = []
    character_sum = 0
    order_counts = {}
    for i, columns in enumerate(elements):
        determinant = (field_product(columns[0] & 3, columns[2] >> 2)
                       ^ field_product(columns[2] & 3, columns[0] >> 2))
        if determinant != 1:
            continue
        special.append(i)
        power, order = i, 1
        while power != 0:
            power = table[power][i]
            order += 1
            assert order <= 5
        order_counts[order] = order_counts.get(order, 0) + 1
        if order in (3, 5):
            character_sum ^= 1 << i
    assert len(special) == 60
    assert order_counts == {1: 1, 2: 15, 3: 20, 5: 24}
    center_norm = (1 ^ basis(scalar)
                   ^ basis(matrix_product(scalar, scalar)))
    steinberg = multiply(center_norm, character_sum)
    assert steinberg.bit_count() == 132
    assert multiply(steinberg, steinberg) == steinberg
    assert all(multiply(steinberg, basis(g)) == multiply(basis(g), steinberg)
               for g in generators)
    assert natural(steinberg) == [0, 0, 0, 0]
    f_common = multiply(f, steinberg)
    p_common = multiply(projector, steinberg)
    f_reduced, p_reduced = f ^ f_common, projector ^ p_common
    conjugator = (13, 6, 9, 14)  # [[I,I],[G^2,G]], over F_2
    conjugator_index = index[conjugator]
    inverse_index = table[conjugator_index].index(0)
    common_forward = multiply(basis(conjugator), f_common)
    common_backward = multiply(f_common, 1 << inverse_index)
    assert multiply(common_backward, common_forward) == f_common
    assert multiply(common_forward, common_backward) == p_common
    assert multiply(p_common, common_forward) == common_forward
    assert multiply(common_forward, f_common) == common_forward
    assert multiply(f_reduced, f_reduced) == f_reduced
    assert multiply(p_reduced, p_reduced) == p_reduced
    assert multiply(f_common, f_reduced) == 0
    assert multiply(p_common, p_reduced) == 0
    assert natural(f_reduced) == [0, 0, 0, 0]
    assert natural(p_reduced) == natural(projector)
    reduced_ranks = {name: regular_rank(value) for name, value in (
        ("E", steinberg), ("f_common", f_common), ("P_common", p_common),
        ("f_reduced", f_reduced), ("P_reduced", p_reduced))}
    assert reduced_ranks == {"E": 16, "f_common": 8, "P_common": 8,
                             "f_reduced": 32, "P_reduced": 32}

    def record(value):
        return {
            "support_size": value.bit_count(),
            "matrix_columns": [list(elements[i]) for i in bits(value)],
            "natural_evaluation_columns": natural(value),
        }

    result = {
        "status": "exact_finite_corner_certificate",
        "scope": "Stable-image split only; no Kaplansky inverse pair found or claimed.",
        "ordered_leaves": ["000", "001", "010", "011"],
        "group_order": len(elements),
        "parent_columns": parent,
        "child_columns": child,
        "minimal_polynomial_exponents": list(bits(minimal)),
        "nilpotent_index": nilpotent_index,
        "regular_factor_exponents": list(bits(regular_factor)),
        "h_polynomial_exponents": list(bits(h_polynomial)),
        "v_polynomial_exponents": list(bits(v_polynomial)),
        "e": record(e), "T": record(target), "h": record(h),
        "v": record(v), "f": record(f),
        "P": record(projector),
        "projector_comparison": {
            "f_plus": "u f_original u^-1; the f recorded above",
            "P": "E_parent + (E_parent E_child E_parent)^4",
            "regular_ranks": ranks,
            "common_lifted_trace": str(Fraction(ranks["P"], len(elements))),
            "finite_group_module_isomorphism_excluded":
                "f_plus acts as zero and P as a rank-two projector on the natural module",
        },
        "steinberg_reduction": {
            "scope": "A sufficient rank-32 target; cancellation over the full group ring is not asserted.",
            "SL2_order_counts": order_counts,
            "E_support_size": steinberg.bit_count(),
            "E_formula": "(1+z+z^2) times the sum of SL2(F4) elements of order 3 or 5",
            "conjugator_columns": conjugator,
            "conjugator_inverse_columns": elements[inverse_index],
            "common_forward_formula": "[conjugator] f_plus E",
            "common_backward_formula": "f_plus E [conjugator^-1]",
            "common_inverse_identities_checked": True,
            "regular_ranks": reduced_ranks,
            "common_reduced_lifted_trace": str(Fraction(32, len(elements))),
            "f_reduced": record(f_reduced),
            "P_reduced": record(p_reduced),
        },
        "all_exact_checks_passed": True,
        "elapsed_seconds": time.monotonic() - start,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in (
        "status", "group_order", "minimal_polynomial_exponents",
        "nilpotent_index", "h_polynomial_exponents", "v_polynomial_exponents",
        "elapsed_seconds")}), flush=True)
    print(json.dumps({name: result[name]["support_size"]
                      for name in ("e", "T", "h", "v", "f", "P")}), flush=True)
    print(json.dumps(result["projector_comparison"]), flush=True)
    print(json.dumps({"steinberg_ranks": reduced_ranks,
                      "reduced_support_sizes": [f_reduced.bit_count(),
                                                p_reduced.bit_count()]}), flush=True)


if __name__ == "__main__":
    main()
