#!/usr/bin/env python3
"""Compress all maximal NC carrier schemes for the three-winner profile.

The four copy-retraction equations are substituted first, leaving eight free
coefficient generators.  The forest recursion deduplicates exact
coordinate-aware Tietze states at every interval instead of materializing the
1.57 million minimum-block boundary partitions (or the larger all-maximal set).
"""

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


C = load("three_winner_compression", "compress-l14-three-winner-projections.py")
P = load("i1412_pairs", "enumerate-l14-i1412-carrier-pairs.py")
ALG = P.EQ3
FREE = ("p", "u", "v", "w", "y", "z", "a", "e")
NUMBER = {name: index + 1 for index, name in enumerate(FREE)}
IDENTITY_IMAGES = tuple((index,) for index in range(1, len(FREE) + 1))


def encode(coefficient):
    return tuple(sign * NUMBER[name] for name, sign in coefficient)


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
                          IDENTITY_IMAGES)


EMPTY_STATE = ((), IDENTITY_IMAGES)


@lru_cache(maxsize=None)
def relation_state(relation):
    return P.close_tietze((relation,), IDENTITY_IMAGES)


def maximal_states(word):
    colors = tuple(copy for copy, _ in word)
    coefficients = tuple(encode(coefficient) for _, coefficient in word)

    @lru_cache(maxsize=None)
    def visit(left, right, forbidden):
        if left >= right:
            return (EMPTY_STATE,)
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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("equation", choices=("eq0", "eq4", "boundary"))
    args = parser.parse_args()
    word = {"eq0": C.EQ0, "eq4": C.EQ4, "boundary": C.K}[args.equation]
    states, intervals = maximal_states(word)
    print(f"equation={args.equation}")
    print(f"syllables={len(word)}")
    print(f"cached_intervals={intervals}")
    print(f"coordinate_tietze_states={len(states)}")
    print(f"abstract_presentations={len(set(residual for residual, _ in states))}")
    for state in states[:100]:
        print(state)


if __name__ == "__main__":
    main()
