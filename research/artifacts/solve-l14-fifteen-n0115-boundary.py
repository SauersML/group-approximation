#!/usr/bin/env python3
"""Exhaust cyclic one-copy boundaries for fifteen-winner N(0;115)."""

import argparse
import importlib.util
from functools import lru_cache
from itertools import combinations
from math import gcd
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


S = load("fifteen_n0115_states",
         "solve-l14-fifteen-n0115-maximal-states.py")
ALG = S.ALG
Q = 9
IDENTITY = tuple((index,) for index in range(1, Q + 1))


def state_relations(state):
    residual, images = state
    definitions = []
    for generator, image in enumerate(images, 1):
        relation = ALG.reduce_word((generator,) + ALG.inverse(image))
        if relation:
            definitions.append(relation)
    return residual + tuple(definitions)


def close_prefer_q(relations, images):
    """Eliminate the once-occurring formal target before generic Tietze moves."""
    relations = list(relations)
    images = list(images)
    for relation_index, relation in enumerate(relations):
        positions = [index for index, letter in enumerate(relation)
                     if abs(letter) == Q]
        if len(positions) != 1:
            continue
        position = positions[0]
        letter = relation[position]
        left, right = relation[:position], relation[position + 1:]
        replacement = (ALG.inverse(left) + ALG.inverse(right)
                       if letter > 0 else right + left)
        replacement = ALG.reduce_word(replacement)
        relations.pop(relation_index)
        relations = [ALG.substitute(word, Q, replacement)
                     for word in relations]
        images = [ALG.substitute(word, Q, replacement) for word in images]
        break
    return S.P.close_tietze(tuple(relations), tuple(images))


@lru_cache(maxsize=None)
def combine(left, right):
    return close_prefer_q(state_relations(left) + state_relations(right),
                          IDENTITY)


EMPTY = ((), IDENTITY)


@lru_cache(maxsize=None)
def relation_state(relation):
    return close_prefer_q((relation,), IDENTITY)


@lru_cache(maxsize=None)
def maximal_states(word):
    colors = tuple(copy for copy, _ in word)
    coefficients = tuple(coefficient for _, coefficient in word)

    @lru_cache(maxsize=None)
    def visit(left, right, forbidden):
        if left >= right:
            return (EMPTY,)
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

    return visit(0, len(word), 0)


def transform(word, images):
    out = ()
    for letter in word:
        image = images[abs(letter) - 1]
        if letter < 0:
            image = ALG.inverse(image)
        out = ALG.reduce_word(out + image)
    return out


def normalize_fp(word):
    out = []
    for copy, coefficient in word:
        if not coefficient:
            continue
        if out and out[-1][0] == copy:
            coefficient = ALG.reduce_word(out[-1][1] + coefficient)
            out.pop()
            if coefficient:
                out.append((copy, coefficient))
        else:
            out.append((copy, coefficient))
    return tuple(out)


def rotations(word):
    pending, seen = [tuple(word)], set()
    while pending:
        candidate = normalize_fp(pending.pop())
        if candidate in seen:
            continue
        seen.add(candidate)
        pending.extend(candidate[offset:] + candidate[:offset]
                       for offset in range(1, len(candidate)))
    return tuple(sorted(seen))


def cyclic_reduce(word):
    word = list(ALG.reduce_word(word))
    while len(word) > 1 and word[0] == -word[-1]:
        word = word[1:-1]
    return tuple(word)


def cyclic_key(word):
    word = cyclic_reduce(word)
    if not word:
        return ()
    variants = []
    for candidate in (word, ALG.inverse(word)):
        variants.extend(candidate[offset:] + candidate[:offset]
                        for offset in range(len(candidate)))
    return min(variants)


def pure_power(word):
    word = cyclic_reduce(word)
    if not word or any(abs(letter) != abs(word[0]) for letter in word):
        return None
    return abs(word[0]), sum(1 if letter > 0 else -1 for letter in word)


def power_killed(q_image, residual):
    target = pure_power(q_image)
    if target is None:
        return False
    generator, exponent = target
    modulus = 0
    for relation in residual:
        power = pure_power(relation)
        if power is not None and power[0] == generator:
            modulus = gcd(modulus, abs(power[1]))
    return modulus != 0 and exponent % modulus == 0


def carrier_states(branch):
    carrier_maximal, words, carrier_combine, encode, _ = S.solver(branch)
    left, _ = carrier_maximal(words["r0"])
    right, _ = carrier_maximal(words["r4"])
    states = tuple(sorted({carrier_combine(a, b) for a in left for b in right}))
    encoded_boundary = tuple((copy, encode(coefficient))
                             for copy, coefficient in words["boundary"])
    return states, encoded_boundary


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("branch", choices=("I", "II"))
    parser.add_argument("--carrier-index", type=int)
    parser.add_argument("--trace", action="store_true")
    args = parser.parse_args()
    carriers, encoded_boundary = carrier_states(args.branch)
    results, augmented_words = set(), set()
    for index, (residual, images8) in enumerate(carriers, 1):
        if args.carrier_index is not None and index != args.carrier_index:
            continue
        transformed = normalize_fp(
            (copy, transform(coefficient, images8))
            for copy, coefficient in encoded_boundary)
        base = residual, images8 + ((Q,),)
        cuts = rotations(transformed)
        if args.trace:
            print(f"carrier={index} cuts={len(cuts)} syllables={len(transformed)}",
                  flush=True)
        for rotation in cuts:
            for target in range(4):
                augmented = normalize_fp(rotation + ((target, (-Q,)),))
                augmented_words.add(augmented)
                for boundary in maximal_states(augmented):
                    final = combine(base, boundary)
                    results.add((target, final[0], final[1][-1], final[1][:-1]))
        if index % 10 == 0 or args.carrier_index is not None:
            print(f"carrier={index} words={len(augmented_words)} states={len(results)}",
                  flush=True)
    nonempty = [state for state in results if state[2]]
    free = [state for state in nonempty if not state[1]]
    direct = [state for state in nonempty
              if cyclic_key(state[2]) in
              {cyclic_key(relation) for relation in state[1]}]
    powers = [state for state in nonempty
              if state not in direct and power_killed(state[2], state[1])]
    unresolved = [state for state in nonempty
                  if state not in direct and state not in powers]
    print(f"branch={args.branch}")
    print(f"carrier_states={len(carriers)}")
    print(f"distinct_augmented_words={len(augmented_words)}")
    print(f"boundary_states={len(results)}")
    print(f"nonempty_q={len(nonempty)}")
    print(f"free_nonempty_q={len(free)}")
    print(f"direct_killed_q={len(direct)}")
    print(f"power_killed_q={len(powers)}")
    print(f"unresolved_q={len(unresolved)}")
    for state in sorted(free)[:100]:
        print("FREE", state)
    for state in sorted(direct)[:100]:
        print("DIRECT", state)
    for state in sorted(powers)[:100]:
        print("POWER", state)
    for state in sorted(unresolved)[:100]:
        print("UNRESOLVED", state)


if __name__ == "__main__":
    main()
