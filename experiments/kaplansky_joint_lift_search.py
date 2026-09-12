"""Exact joint lift search for a strict one-sided unit in F2[Q].

Choose sparse affine lifts ``b`` of the Leavitt generator ``t0``.  For each
one, solve a single linear system for an ``a`` satisfying simultaneously

    b*a = 1  in the literal group algebra F2[Q],
    evaluation(a) = s0 in the Leavitt algebra.

A hit is automatically strict after reversing the product, since its Leavitt
evaluation is ``s0*t0 != 1``.  Thus a hit is a complete finite certificate for
failure of Kaplansky direct finiteness and Gottschalk surjunctivity.  A miss is
only a bounded/randomized fence.
"""

import argparse
import random

from depth_one_paired_leavitt_return_search import ONE, canonical, equal
from kaplansky_affine_lift_search import affine_leavitt_solutions
from kaplansky_asymmetric_atlas_search import (
    S0,
    cayley_ball,
    evaluate_sum,
    expanded_terms,
    group_algebra_product,
    key,
    multiply_keys,
)


T0 = canonical((("", "0"),))


def descend(value, dependencies):
    while True:
        successor = min(
            (value ^ dependency for dependency in dependencies),
            key=int.bit_count,
        )
        if successor.bit_count() >= value.bit_count():
            return value
        value = successor


def sparse_affine_samples(particular, dependencies, count, seed):
    rng = random.Random(seed)
    samples = {descend(particular, dependencies)}
    attempts = max(1000, 80 * count)
    for _ in range(attempts):
        value = particular
        for _ in range(rng.randrange(1, 24)):
            value ^= rng.choice(dependencies)
        samples.add(descend(value, dependencies))
    return sorted(samples, key=lambda value: (value.bit_count(), value))[:count]


def solve_joint_right_factor(b_support, a_ball):
    """Solve b*a=1 and evaluation(a)=s0 over F2 in one exact system."""
    product_supports = []
    group_universe = {key(ONE)}
    b_keys = tuple(key(value) for value in b_support)
    for candidate in a_ball:
        support = set()
        candidate_key = key(candidate)
        for b_key in b_keys:
            term = multiply_keys(b_key, candidate_key)
            if term in support:
                support.remove(term)
            else:
                support.add(term)
        product_supports.append(support)
        group_universe.update(support)
    group_coordinate = {
        term: i for i, term in enumerate(sorted(group_universe))
    }

    depth = max(
        [len(nu) for value in a_ball + [S0] for _, nu in value],
        default=0,
    )
    expanded = [expanded_terms(value, depth) for value in a_ball + [S0]]
    leavitt_universe = {term for terms in expanded for term in terms}
    leavitt_coordinate = {
        term: i for i, term in enumerate(sorted(leavitt_universe))
    }
    offset = len(group_coordinate)

    columns = []
    for group_terms, leavitt_terms in zip(product_supports, expanded[:-1]):
        vector = 0
        for term in group_terms:
            vector ^= 1 << group_coordinate[term]
        for term in leavitt_terms:
            vector ^= 1 << (offset + leavitt_coordinate[term])
        columns.append(vector)

    target = 1 << group_coordinate[key(ONE)]
    for term in expanded[-1]:
        target ^= 1 << (offset + leavitt_coordinate[term])

    basis = {}
    for index, vector in enumerate(columns):
        combination = 1 << index
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (vector, combination)
                break
            vector ^= basis[pivot][0]
            combination ^= basis[pivot][1]

    combination = 0
    while target:
        pivot = target.bit_length() - 1
        if pivot not in basis:
            return None
        target ^= basis[pivot][0]
        combination ^= basis[pivot][1]
    return tuple(
        i for i in range(len(a_ball)) if (combination >> i) & 1
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lift-radius", type=int, default=3)
    parser.add_argument("--a-radius", type=int, default=3)
    parser.add_argument("--samples", type=int, default=128)
    parser.add_argument("--seed", type=int, default=20260907)
    args = parser.parse_args()

    _, lift_ball, lift_words = cayley_ball(args.lift_radius)
    particular, dependencies = affine_leavitt_solutions(lift_ball, T0, parity=1)
    if particular is None:
        print("NO_T0_LIFT")
        return
    samples = sparse_affine_samples(
        particular, dependencies, args.samples, args.seed
    )
    _, a_ball, a_words = cayley_ball(args.a_radius)
    print("lift ball", len(lift_ball), "a ball", len(a_ball))
    print("kernel dimension", len(dependencies), "samples", len(samples))
    print("b support range", samples[0].bit_count(), samples[-1].bit_count())

    for trial, sample in enumerate(samples, 1):
        b_support = [
            value for i, value in enumerate(lift_ball) if (sample >> i) & 1
        ]
        assert len(b_support) % 2 == 1
        assert equal(evaluate_sum(b_support), T0)
        inverse = solve_joint_right_factor(b_support, a_ball)
        if trial == 1 or trial % 10 == 0:
            print("trial", trial, "b support", len(b_support), flush=True)
        if inverse is None:
            continue

        a_support = [a_ball[i] for i in inverse]
        assert equal(evaluate_sum(a_support), S0)
        forward = group_algebra_product(b_support, a_support)
        reverse = group_algebra_product(a_support, b_support)
        assert forward == {key(ONE)}
        assert reverse != {key(ONE)}
        print("COUNTEREXAMPLE_FOUND")
        print("b words", [
            lift_words[i] for i in range(len(lift_ball)) if (sample >> i) & 1
        ])
        print("a words", [a_words[i] for i in inverse])
        print("a support", len(a_support), "b support", len(b_support))
        print("reverse support", len(reverse))
        return
    print("NO_JOINT_SOLUTION_IN_SAMPLED_FAMILY")


if __name__ == "__main__":
    main()
