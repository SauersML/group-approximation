"""Seek a literal Kaplansky witness by correcting a finite unipotent product.

For the full-support eleven-term lift A of s0, solve B*A=q where q has odd
augmentation and support in an elementary abelian 2-subgroup U. Then q*q=1,
so (q*B)*A=1. Every hit is checked by exact group-algebra multiplication.
Run on MSI only. A miss describes just the displayed finite search.
"""

import argparse
from itertools import combinations
import json
import time

from atlas_two_chart_search import I4
from depth_one_paired_leavitt_return_search import ONE, equal, multiply
from kaplansky_asymmetric_atlas_search import (
    S0, atlas_generators, cayley_ball, chart_value, evaluate_sum,
    from_key, group_algebra_product, key, multiply_keys,
)


A_WORDS = (
    (0, 1, 2), (3, 5, 4), (6, 7, 8), (9, 11, 10),
    (1, 0), (6, 8), (0, 2, 9), (3, 1, 7),
    (5, 3, 1), (5, 3, 4), (5, 11, 10),
)


def unipotent_subgroups():
    """All row, column, and 2+2 square-zero block groups in both charts."""
    for chart in (1, 2):
        for size in (1, 2, 3):
            for rows in combinations(range(4), size):
                columns = tuple(i for i in range(4) if i not in rows)
                cells = tuple((i, j) for i in rows for j in columns)
                elements = []
                for mask in range(1 << len(cells)):
                    matrix = I4.copy()
                    for bit, (i, j) in enumerate(cells):
                        if (mask >> bit) & 1:
                            matrix[i, j] ^= 1
                    elements.append(key(chart_value(chart, matrix)))
                assert len(set(elements)) == 1 << len(cells)
                yield (chart, rows), tuple(elements)


def reduce_vector(value, combination, basis):
    while value:
        pivot = value.bit_length() - 1
        if pivot not in basis:
            break
        row, witness = basis[pivot]
        value ^= row
        combination ^= witness
    return value, combination


def literal_product(left, right):
    """Recompute without using the memoized group-product routine."""
    result = set()
    for x in left:
        for y in right:
            term = key(multiply(from_key(x), from_key(y)))
            if term in result:
                result.remove(term)
            else:
                result.add(term)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--partner-radius", type=int, default=3)
    parser.add_argument("--seconds", type=float, default=45)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    started = time.monotonic()
    identity = key(ONE)
    generators = tuple(key(g) for _, g in atlas_generators())
    a_keys = []
    for word in A_WORDS:
        value = identity
        for index in word:
            value = multiply_keys(value, generators[index])
        a_keys.append(value)
    assert len(set(a_keys)) == 11
    a_support = [from_key(value) for value in a_keys]
    assert equal(evaluate_sum(a_support), S0)

    _, ball, words = cayley_ball(args.partner_radius)
    groups = list(unipotent_subgroups())
    universe = {g for _, elements in groups for g in elements}
    products = []
    for candidate in ball:
        terms = {multiply_keys(key(candidate), a) for a in a_keys}
        assert len(terms) == 11
        products.append(terms)
        universe.update(terms)
        if time.monotonic() - started > args.seconds:
            result = {"status": "budget_expired_during_products",
                      "computed_columns": len(products), "ball": len(ball)}
            break
    else:
        coordinates = {g: i for i, g in enumerate(sorted(universe))}
        basis = {}
        for index, terms in enumerate(products):
            vector = sum(1 << coordinates[g] for g in terms)
            vector, witness = reduce_vector(vector, 1 << index, basis)
            if vector:
                basis[vector.bit_length() - 1] = vector, witness

        target = 1 << coordinates[identity]
        tested = []
        result = {"status": "no_hit", "ball": len(ball),
                  "product_coordinates": len(coordinates),
                  "product_span_rank": len(basis), "tested": tested}
        for name, elements in groups:
            if time.monotonic() - started > args.seconds:
                result["status"] = "budget_expired_between_subgroups"
                break
            extended = basis.copy()
            for index, g in enumerate(x for x in elements if x != identity):
                vector = target ^ (1 << coordinates[g])
                vector, witness = reduce_vector(
                    vector, 1 << (len(ball) + index), extended)
                if vector:
                    extended[vector.bit_length() - 1] = vector, witness
            remainder, witness = reduce_vector(target, 0, extended)
            tested.append({"chart": name[0], "rows": name[1],
                           "order": len(elements),
                           "extended_rank": len(extended),
                           "solvable": remainder == 0})
            if remainder:
                continue

            b_indices = [i for i in range(len(ball)) if (witness >> i) & 1]
            b_keys = [key(ball[i]) for i in b_indices]
            q_keys = literal_product(b_keys, a_keys)
            assert q_keys <= set(elements)
            assert len(q_keys) % 2 == 1
            assert literal_product(q_keys, q_keys) == {identity}
            corrected_b = literal_product(q_keys, b_keys)
            forward = literal_product(corrected_b, a_keys)
            reverse = literal_product(a_keys, corrected_b)
            assert forward == {identity}
            assert reverse != {identity}
            assert group_algebra_product(
                [from_key(g) for g in corrected_b], a_support) == {identity}
            assert not equal(multiply(S0, evaluate_sum(
                [from_key(g) for g in corrected_b])), ONE)
            result.update(status="COUNTEREXAMPLE_FOUND", a_words=A_WORDS,
                          b_words=[words[i] for i in b_indices],
                          q_keys=sorted(q_keys), corrected_b=sorted(corrected_b),
                          reverse_keys=sorted(reverse))
            break

    result["elapsed_seconds"] = time.monotonic() - started
    result["partner_radius"] = args.partner_radius
    with open(args.output, "w") as stream:
        json.dump(result, stream, indent=2)
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
