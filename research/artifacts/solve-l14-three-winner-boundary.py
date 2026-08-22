#!/usr/bin/env python3
"""Exhaust cyclic one-copy boundaries over all three-winner carrier states."""

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


S = load("three_winner_states", "solve-l14-three-winner-maximal-states.py")
C, ALG = S.C, S.ALG
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


@lru_cache(maxsize=None)
def combine(left, right):
    return S.P.close_tietze(state_relations(left) + state_relations(right), IDENTITY)


EMPTY = ((), IDENTITY)


@lru_cache(maxsize=None)
def relation_state(relation):
    return S.P.close_tietze((relation,), IDENTITY)


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


ENCODED_K = tuple((copy, S.encode(coefficient)) for copy, coefficient in C.K)


def main():
    carriers = S.combined_carrier_states(report=True)
    results = set()
    augmented_words = set()
    for index, (residual, images) in enumerate(carriers, 1):
        transformed = normalize_fp((copy, transform(coefficient, images))
                                   for copy, coefficient in ENCODED_K)
        base = residual, images + ((Q,),)
        for rotation in rotations(transformed):
            for target in range(4):
                augmented = normalize_fp(rotation + ((target, (-Q,)),))
                augmented_words.add(augmented)
                for boundary in maximal_states(augmented):
                    final = combine(base, boundary)
                    results.add((target, final[0], final[1][-1], final[1][:-1]))
        if index % 25 == 0:
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
    print(f"distinct_augmented_words={len(augmented_words)}")
    print(f"boundary_states={len(results)}")
    print(f"nonempty_q={len(nonempty)}")
    print(f"free_nonempty_q={len(free)}")
    print(f"direct_killed_q={len(direct)}")
    print(f"power_killed_q={len(powers)}")
    print(f"unresolved_q={len(unresolved)}")
    for state in sorted(free)[:100]:
        print("FREE", state)
    for state in sorted(unresolved)[:100]:
        print("UNRESOLVED", state)


if __name__ == "__main__":
    main()
