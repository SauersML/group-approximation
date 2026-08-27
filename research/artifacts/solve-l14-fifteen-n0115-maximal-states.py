#!/usr/bin/env python3
"""Enumerate exact all-maximal carrier states for fifteen-winner N(0;115)."""

import argparse
import importlib.util
from functools import lru_cache
from itertools import combinations
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


C = load("fifteen_n0115_compression",
         "compress-l14-fifteen-n0115-projections.py")
P = load("i1412_pairs", "enumerate-l14-i1412-carrier-pairs.py")
ALG = P.EQ3


def build_solver(compression, branch, free, power_names):
    number = {name: index + 1 for index, name in enumerate(free)}
    identity_images = tuple((index,) for index in range(1, len(free) + 1))
    base_relations = tuple((number[name], number[name])
                           for name in power_names)

    def encode(coefficient):
        return tuple(sign * number[name] for name, sign in coefficient)

    def state_relations(state):
        residual, images = state
        definitions = []
        for generator, image in enumerate(images, 1):
            relation = ALG.reduce_word((generator,) + ALG.inverse(image))
            if relation:
                definitions.append(relation)
        return residual + tuple(definitions)

    @lru_cache(maxsize=None)
    def combine(left, right):
        return P.close_tietze(state_relations(left) + state_relations(right),
                              identity_images)

    @lru_cache(maxsize=None)
    def relation_state(relation):
        return P.close_tietze(base_relations + (relation,), identity_images)

    empty_state = P.close_tietze(base_relations, identity_images)

    def maximal_states(word, encoded=False):
        colors = tuple(copy for copy, _ in word)
        coefficients = tuple(coefficient if encoded else encode(coefficient)
                             for _, coefficient in word)

        @lru_cache(maxsize=None)
        def visit(left, right, forbidden):
            if left >= right:
                return (empty_state,)
            color = colors[left]
            if forbidden & (1 << color):
                return ()
            peers = [index for index in range(left + 1, right)
                     if colors[index] == color]
            answers = set()
            for width in range(len(peers) + 1):
                for tail in combinations(peers, width):
                    block = (left,) + tail
                    block_word = ALG.reduce_word(sum(
                        (coefficients[index] for index in block), ()))
                    states = {relation_state(block_word)}
                    previous, valid = left, True
                    for bound in tail:
                        choices = visit(previous + 1, bound, 1 << color)
                        if not choices:
                            valid = False
                            break
                        states = {combine(prefix, choice)
                                  for prefix in states for choice in choices}
                        previous = bound
                    if not valid:
                        continue
                    suffixes = visit(previous + 1, right,
                                     forbidden | (1 << color))
                    answers.update(combine(prefix, suffix)
                                   for prefix in states for suffix in suffixes)
            return tuple(sorted(answers))

        states = visit(0, len(word), 0)
        return states, visit.cache_info().currsize

    words = {
        "r0": compression.branch_reduce(compression.R0, branch),
        "r4": compression.branch_reduce(compression.R4, branch),
        "boundary": compression.branch_reduce(compression.K, branch),
    }
    return maximal_states, words, combine, encode, identity_images


def solver(branch):
    free = (("q", "r", "s", "t", "u", "A", "B", "E")
            if branch == "I" else
            ("q", "r", "s", "u", "A", "B", "C", "E"))
    powers = (("A", "B", "E", "s") if branch == "I" else
              ("A", "B", "C", "E"))
    return build_solver(C, branch, free, powers)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("branch", choices=("I", "II"))
    parser.add_argument("equation", choices=("r0", "r4", "both", "boundary"))
    args = parser.parse_args()
    maximal_states, words, combine, _, _ = solver(args.branch)
    if args.equation == "both":
        left, left_intervals = maximal_states(words["r0"])
        right, right_intervals = maximal_states(words["r4"])
        states = tuple(sorted({combine(a, b) for a in left for b in right}))
        print(f"branch={args.branch}")
        print(f"r0_states={len(left)}")
        print(f"r4_states={len(right)}")
        print(f"cached_intervals={left_intervals + right_intervals}")
        print(f"combined_coordinate_states={len(states)}")
    else:
        states, intervals = maximal_states(words[args.equation])
        print(f"branch={args.branch}")
        print(f"equation={args.equation}")
        print(f"syllables={len(words[args.equation])}")
        print(f"cached_intervals={intervals}")
        print(f"coordinate_tietze_states={len(states)}")
    print(f"abstract_presentations={len(set(r for r, _ in states))}")
    for state in states[:100]:
        print(state)


if __name__ == "__main__":
    main()
