"""Search an affine family of exact cross-atlas lifts for a one-sided unit.

The earlier bounded experiment selected one arbitrary solution of

    evaluation(a) = s_0.

That discards the large kernel of the evaluation map.  Here we compute exact
kernel dependencies over F_2, rank nearby affine solutions by support size,
and test each of them against the literal group-algebra equation b*a=1.
Every reported hit is independently multiplied in the exact Leavitt prefix
normal form.  A negative result is only a bounded computational fence.
"""

import argparse
from itertools import combinations

from depth_one_paired_leavitt_return_search import ONE, add, equal, multiply
from atlas_two_chart_search import I4, factor_generators, gf2_mul
from kaplansky_asymmetric_atlas_search import (
    S0,
    atlas_generators,
    cayley_ball,
    chart_value,
    evaluate_sum,
    expanded_terms,
    group_algebra_product,
    key,
    solve_left_inverse,
)


def four_generator_atlas():
    """Two exact generators for each GL(4,2) chart, hence four for Q."""
    adjacent = [word[0][1] for _, word in factor_generators()[:6]]

    def matrix_word(indices):
        value = I4.copy()
        for index in indices:
            value = gf2_mul(value, adjacent[index])
        return value

    words = ((0, 1, 2), (3, 5, 4))
    return tuple(
        (f"chart{factor}_{''.join(map(str, word))}",
         chart_value(factor, matrix_word(word)))
        for factor in (1, 2)
        for word in words
    )


def affine_leavitt_solutions(columns, target, parity):
    """Return one solution bitset and a spanning list of kernel bitsets."""
    depth = max(
        [len(nu) for value in columns + [target] for _, nu in value],
        default=0,
    )
    expanded = [expanded_terms(value, depth) for value in columns + [target]]
    all_terms = set().union(*expanded)
    coordinate = {term: i for i, term in enumerate(sorted(all_terms))}
    parity_bit = len(coordinate)

    def vector(terms, extra):
        value = (extra & 1) << parity_bit
        for term in terms:
            value ^= 1 << coordinate[term]
        return value

    basis = {}
    dependencies = []
    for index, terms in enumerate(expanded[:-1]):
        value = vector(terms, 1)
        combination = 1 << index
        while value:
            pivot = value.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (value, combination)
                break
            value ^= basis[pivot][0]
            combination ^= basis[pivot][1]
        if value == 0:
            dependencies.append(combination)

    value = vector(expanded[-1], parity)
    particular = 0
    while value:
        pivot = value.bit_length() - 1
        if pivot not in basis:
            return None, ()
        value ^= basis[pivot][0]
        particular ^= basis[pivot][1]
    return particular, tuple(dependencies)


def ranked_variants(particular, dependencies, limit, pair_pool):
    """Enumerate support-small affine variants from sparse kernel moves."""
    candidates = {particular}
    single = sorted(
        (particular ^ dependency for dependency in dependencies),
        key=lambda value: (value.bit_count(), value),
    )
    candidates.update(single[: max(limit, pair_pool)])

    # A pair can cancel pieces that neither single move removes.  Restrict to
    # the best single moves so the enumeration remains deterministic.
    moves = [particular ^ value for value in single[:pair_pool]]
    for left, right in combinations(moves, 2):
        candidates.add(particular ^ left ^ right)

    return sorted(candidates, key=lambda value: (value.bit_count(), value))[:limit]


def selected_values(bitset, values):
    return [value for i, value in enumerate(values) if (bitset >> i) & 1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lift-radius", type=int, default=3)
    parser.add_argument("--inverse-radius", type=int, default=2)
    parser.add_argument("--trials", type=int, default=256)
    parser.add_argument("--pair-pool", type=int, default=40)
    parser.add_argument(
        "--mandatory", choices=("atlas4", "atlas12"), default="atlas4"
    )
    args = parser.parse_args()

    generators = four_generator_atlas() if args.mandatory == "atlas4" else atlas_generators()
    mandatory = [value for _, value in generators]
    mandatory_keys = {key(value) for value in mandatory}
    mandatory_sum = evaluate_sum(mandatory)
    residual = add(S0, mandatory_sum)

    _, lift_ball, lift_words = cayley_ball(args.lift_radius)
    records = [
        (value, word)
        for value, word in zip(lift_ball, lift_words)
        if key(value) not in mandatory_keys
    ]
    candidates = [value for value, _ in records]
    particular, dependencies = affine_leavitt_solutions(
        candidates, residual, parity=1
    )
    if particular is None:
        print("NO_FORCED_S0_LIFT")
        return

    variants = ranked_variants(
        particular, dependencies, args.trials, args.pair_pool
    )
    _, inverse_ball, inverse_words = cayley_ball(args.inverse_radius)
    print("lift ball", len(lift_ball), "inverse ball", len(inverse_ball))
    print("kernel dimension", len(dependencies), "variants", len(variants))
    print("extra-support range", variants[0].bit_count(), variants[-1].bit_count())
    best = variants[0]
    print("best exact s0 lift support", len(mandatory) + best.bit_count())
    print("best mandatory", [name for name, _ in generators])
    print("best extra words", [
        records[i][1] for i in range(len(records)) if (best >> i) & 1
    ])

    for trial, variant in enumerate(variants, 1):
        a_support = mandatory + selected_values(variant, candidates)
        assert len(a_support) % 2 == 1
        assert equal(evaluate_sum(a_support), S0)
        inverse = solve_left_inverse(inverse_ball, a_support)
        if trial == 1 or trial % 25 == 0:
            print("trial", trial, "a support", len(a_support), flush=True)
        if inverse is None:
            continue

        b_support = [inverse_ball[i] for i in inverse]
        forward = group_algebra_product(b_support, a_support)
        reverse = group_algebra_product(a_support, b_support)
        assert forward == {key(ONE)}
        b_value = evaluate_sum(b_support)
        assert equal(multiply(b_value, S0), ONE)
        assert not equal(multiply(S0, b_value), ONE)
        assert reverse != {key(ONE)}
        print("COUNTEREXAMPLE_FOUND")
        print("mandatory", [name for name, _ in generators])
        print("a words", [name for name, _ in generators] + [
            records[i][1] for i in range(len(records)) if (variant >> i) & 1
        ])
        print("b words", [inverse_words[i] for i in inverse])
        print("a support", len(a_support), "b support", len(b_support))
        print("reverse support", len(reverse))
        return
    print("NO_LEFT_INVERSE_IN_AFFINE_FAMILY")


if __name__ == "__main__":
    main()
