"""Exact prefix-corner triangularization seed for Kaplansky, run on MSI.

A fixed LEFT kernel shear inserts the full Leavitt actor into the fixed
inverse factor. An unknown RIGHT shear N=(1-e)*a*e is square-zero. Solve
(1-e)*W0*N=(1-e)*W0*e. Then W=W0*(1+N) is an explicit unit preserving e.
Its fixed inverse corner has a nonzero evaluated right annihilator,
so every solution gives a strict inverse pair after padding. The
single-shear version has an amenable fixed-factor obstruction and is not run.
"""

import argparse
import json
import time

from depth_one_paired_leavitt_return_search import (
    ONE, ZERO, add, canonical, equal, multiply,
)
from kaplansky_asymmetric_atlas_search import (
    atlas_generators, cayley_ball, evaluate_sum, from_key, key, multiply_keys,
)
from kaplansky_unipotent_product_search import A_WORDS, literal_product


def product(left, right):
    result = set()
    for x in left:
        for y in right:
            value = multiply_keys(x, y)
            if value in result:
                result.remove(value)
            else:
                result.add(value)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=23)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    started = time.monotonic()
    identity = key(ONE)
    p = canonical((("0", "0"),))
    p00 = canonical((("00", "00"),))
    g = canonical((("", ""), ("00", "01"),
                   ("01", "00"), ("00", "00")))
    g2 = multiply(g, g)
    assert equal(multiply(g2, g), ONE)
    assert not equal(g, ONE)
    e = {key(g), key(g2)}
    complement = {identity} ^ e
    assert product(e, e) == e
    assert product(e, complement) == set()
    assert product(complement, e) == set()
    assert equal(evaluate_sum([from_key(x) for x in e]), p)

    u = canonical((("00", "0"), ("01", "10"), ("1", "11")))
    u_inverse = canonical((("0", "00"), ("10", "01"), ("11", "1")))
    assert equal(multiply(u, u_inverse), ONE)
    assert equal(multiply(u_inverse, u), ONE)
    assert equal(multiply(multiply(u, p), u_inverse), p00)
    assert not equal(p00, p)
    u_key, inverse_key = key(u), key(u_inverse)

    generators = tuple(key(value) for _, value in atlas_generators())

    def word_value(word):
        value = identity
        for index in word:
            value = multiply_keys(value, generators[index])
        return value

    actors = (identity,) + tuple(word_value(word) for word in A_WORDS[:4])
    d_kernel = product({identity, generators[1]}, {identity, generators[4]})
    assert equal(evaluate_sum([from_key(x) for x in d_kernel]), ZERO)
    k_kernel = product(set(actors), d_kernel)
    n_left = product(product(complement, k_kernel), e)
    assert n_left
    assert equal(evaluate_sum([from_key(x) for x in n_left]), ZERO)
    # N_left^2=0 follows from the checked middle product e*(1-e)=0.
    # The full coefficient products are independently rechecked on a hit.
    w0 = {u_key} ^ product(n_left, {u_key})
    w0_inverse = {inverse_key} ^ product({inverse_key}, n_left)
    fixed_b = product(product(e, w0_inverse), e)
    b_evaluation = evaluate_sum([from_key(x) for x in fixed_b])
    assert equal(b_evaluation, multiply(multiply(p, u_inverse), p))
    annihilator = add(p, p00)
    assert not equal(annihilator, ZERO)
    assert equal(multiply(b_evaluation, annihilator), ZERO)

    # If l*q_i*r all survive for i=0,...,4, their ratios to l*r are
    # r^-1*q_i*r. These generate the full actor Q, with no subgroup BFS.
    left_contexts = product(product(e, {inverse_key}), complement)
    right_contexts = product(d_kernel, e)
    support_certificate = None
    for l_value in sorted(left_contexts):
        for r_value in sorted(right_contexts):
            marked_terms = tuple(multiply_keys(multiply_keys(l_value, actor), r_value)
                                 for actor in actors)
            if len(set(marked_terms)) == 5 and set(marked_terms) <= fixed_b:
                support_certificate = {
                    "left": l_value, "right": r_value, "marked_terms": marked_terms,
                }
                break
        if support_certificate is not None:
            break
    result = {"status": "checking_fixed_factor", "fixed_b_support": len(fixed_b),
              "left_shear_support": len(n_left), "support_certificate": support_certificate,
              "right_shear_evaluation_constrained": False,
              "checks": []}

    def record():
        result["elapsed_seconds"] = time.monotonic() - started
        with open(args.output, "w") as stream:
            json.dump(result, stream, indent=2)

    record()
    if support_certificate is None:
        result["status"] = "fixed_factor_full_actor_certificate_failed"
        record()
        print(json.dumps(result), flush=True)
        return

    left = product(complement, w0)
    target = product(left, e)
    assert target
    column_cache = {}
    for radius in (2, 3):
        if radius == 3 and time.monotonic() - started >= 10:
            result["status"] = "radius_three_not_started_after_slow_radius_two"
            break
        _, ball, words = cayley_ball(radius)
        columns, n_columns = [], []
        group_universe = set(target)
        result.update(status="building_columns", a_universe=len(ball), a_radius=radius,
                      completed_columns=0)
        record()
        for value in ball:
            value_key = key(value)
            if value_key not in column_cache:
                n_column = product(product(complement, {value_key}), e)
                column = product(left, n_column)
                column_cache[value_key] = n_column, column
            n_column, column = column_cache[value_key]
            n_columns.append(n_column)
            columns.append(column)
            group_universe.update(column)
            result["completed_columns"] = len(columns)
            if time.monotonic() - started > args.seconds:
                result["status"] = "budget_expired_during_columns"
                record()
                print(json.dumps(result), flush=True)
                return

        group_coordinate = {value: i for i, value in enumerate(sorted(group_universe))}
        basis = {}
        for index, column in enumerate(columns):
            vector = sum(1 << group_coordinate[x] for x in column)
            witness = 1 << index
            while vector:
                pivot = vector.bit_length() - 1
                if pivot not in basis:
                    basis[pivot] = vector, witness
                    break
                row, old_witness = basis[pivot]
                vector ^= row
                witness ^= old_witness

        vector = sum(1 << group_coordinate[x] for x in target)
        witness = 0
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in basis:
                break
            row, old_witness = basis[pivot]
            vector ^= row
            witness ^= old_witness

        result["checks"].append({"radius": radius, "a_universe": len(ball),
                                  "group_coordinates": len(group_coordinate),
                                  "rank": len(basis), "solvable": not bool(vector)})
        record()
        if vector:
            continue
        indices = [i for i in range(len(ball)) if (witness >> i) & 1]
        assert literal_product(n_left, n_left) == set()
        assert literal_product(w0, w0_inverse) == {identity}
        assert literal_product(w0_inverse, w0) == {identity}
        n = set()
        for index in indices:
            n.symmetric_difference_update(n_columns[index])
        assert literal_product(n, n) == set()
        w = w0 ^ literal_product(w0, n)
        w_inverse = w0_inverse ^ literal_product(n, w0_inverse)
        assert literal_product(w, w_inverse) == {identity}
        assert literal_product(w_inverse, w) == {identity}
        assert literal_product(literal_product(complement, w), e) == set()
        a = literal_product(literal_product(e, w), e)
        b = literal_product(literal_product(e, w_inverse), e)
        assert b == fixed_b
        assert literal_product(b, a) == e
        assert literal_product(a, b) != e
        assert not equal(evaluate_sum([
            from_key(x) for x in literal_product(a, b)]), p)
        a_padded, b_padded = a ^ complement, b ^ complement
        assert literal_product(b_padded, a_padded) == {identity}
        reverse = literal_product(a_padded, b_padded)
        assert reverse != {identity}
        result.update(status="COUNTEREXAMPLE_FOUND", a_parameter_words=[words[i] for i in indices],
                      a_padded=sorted(a_padded), b_padded=sorted(b_padded),
                      reverse_keys=sorted(reverse))
        record()
        print(json.dumps(result), flush=True)
        return
    else:
        result["status"] = "no_shear_in_both_prescribed_universes"
    record()
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
