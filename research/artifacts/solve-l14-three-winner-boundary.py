#!/usr/bin/env python3
"""Exhaust cyclic one-copy boundaries over all three-winner carrier states."""

import argparse
import importlib.util
from functools import lru_cache
from itertools import combinations
from math import gcd
from pathlib import Path
from time import monotonic


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


def close_prefer_q(relations, images):
    """Eliminate the once-occurring formal target before other Tietze moves."""
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
        relations = [ALG.substitute(word, Q, replacement) for word in relations]
        images = [ALG.substitute(word, Q, replacement) for word in images]
        break
    return S.P.close_tietze(tuple(relations), tuple(images))


@lru_cache(maxsize=None)
def combine(left, right):
    return close_prefer_q(state_relations(left) + state_relations(right), IDENTITY)


@lru_cache(maxsize=None)
def relation_state(relation):
    return close_prefer_q((relation,), IDENTITY)


@lru_cache(maxsize=None)
def maximal_states_relative(word, base):
    """All forest states, canonicalized modulo a fixed carrier state."""
    colors = tuple(copy for copy, _ in word)
    coefficients = tuple(coefficient for _, coefficient in word)

    @lru_cache(maxsize=None)
    def visit(left, right, forbidden):
        if left >= right:
            return (base,)
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
                states = {combine(base, relation_state(block_word))}
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


def primitive_power(word):
    word = cyclic_key(word)
    if not word:
        return None
    for period in range(1, len(word) + 1):
        if len(word) % period == 0:
            root = word[:period]
            exponent = len(word) // period
            if root * exponent == word:
                return root, exponent
    raise AssertionError("finite word has no primitive period")


def power_killed(q_image, residual):
    target = primitive_power(q_image)
    if target is None:
        return False
    root, exponent = target
    modulus = 0
    for relation in residual:
        power = primitive_power(relation)
        if power is not None and power[0] == root:
            modulus = gcd(modulus, abs(power[1]))
    return modulus != 0 and exponent % modulus == 0


def saturate_primitive_roots(q_image, residual):
    """Iteratively adjoin roots whose relator exponents have gcd one."""
    q_image, residual = tuple(q_image), tuple(residual)
    while True:
        moduli = {}
        for relation in residual:
            power = primitive_power(relation)
            if power is None:
                continue
            root, exponent = power
            moduli[root] = gcd(moduli.get(root, 0), exponent)
        roots = tuple(root for root, modulus in sorted(moduli.items())
                      if modulus == 1)
        if not roots:
            return q_image, residual
        closed_residual, images = S.P.close_tietze(residual + roots, IDENTITY)
        closed_q = transform(q_image, images)
        if (closed_q, closed_residual) == (q_image, residual):
            return q_image, residual
        q_image, residual = closed_q, closed_residual


ENCODED_K = tuple((copy, S.encode(coefficient)) for copy, coefficient in C.K)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--carrier-index", type=int)
    parser.add_argument("--carrier-start", type=int)
    parser.add_argument("--carrier-end", type=int)
    parser.add_argument("--trace-words", action="store_true")
    args = parser.parse_args()
    carriers = S.combined_carrier_states(report=True)
    results = set()
    augmented_words = set()
    for index, (residual, images) in enumerate(carriers, 1):
        if args.carrier_index is not None and index != args.carrier_index:
            continue
        if args.carrier_start is not None and index < args.carrier_start:
            continue
        if args.carrier_end is not None and index > args.carrier_end:
            continue
        transformed = normalize_fp((copy, transform(coefficient, images))
                                   for copy, coefficient in ENCODED_K)
        base = residual, images + ((Q,),)
        cuts = rotations(transformed)
        if args.trace_words:
            print(f"TRACE carrier={index} rotations={len(cuts)} "
                  f"syllables={len(transformed)}", flush=True)
        for rotation_index, rotation in enumerate(cuts):
            for target in range(4):
                augmented = normalize_fp(rotation + ((target, (-Q,)),))
                augmented_words.add(augmented)
                started = monotonic()
                boundary_choices = maximal_states_relative(augmented, base)
                if args.trace_words:
                    print(f"TRACE carrier={index} rotation={rotation_index} "
                          f"target={target} syllables={len(augmented)} "
                          f"forest_states={len(boundary_choices)} "
                          f"seconds={monotonic() - started:.3f}", flush=True)
                for final in boundary_choices:
                    results.add((target, final[0], final[1][-1], final[1][:-1]))
        if (index % 25 == 0 or args.carrier_index is not None
                or args.carrier_start is not None):
            print(f"carrier={index} words={len(augmented_words)} states={len(results)}",
                  flush=True)
    nonempty = [state for state in results if state[2]]
    free = [state for state in nonempty if not state[1]]
    direct = [state for state in nonempty
              if cyclic_key(state[2]) in
              {cyclic_key(relation) for relation in state[1]}]
    powers = [state for state in nonempty
              if state not in direct and power_killed(state[2], state[1])]
    saturated = []
    saturation_images = {}
    for state in nonempty:
        if state in direct or state in powers:
            continue
        reduced_q, reduced_residual = saturate_primitive_roots(state[2], state[1])
        saturation_images[state] = (reduced_q, reduced_residual)
        if (not reduced_q
                or cyclic_key(reduced_q) in
                {cyclic_key(relation) for relation in reduced_residual}
                or power_killed(reduced_q, reduced_residual)):
            saturated.append(state)
    unresolved = [state for state in nonempty
                  if state not in direct and state not in powers
                  and state not in saturated]
    print(f"distinct_augmented_words={len(augmented_words)}")
    print(f"boundary_states={len(results)}")
    print(f"nonempty_q={len(nonempty)}")
    print(f"free_nonempty_q={len(free)}")
    print(f"direct_killed_q={len(direct)}")
    print(f"power_killed_q={len(powers)}")
    print(f"saturation_killed_q={len(saturated)}")
    print(f"unresolved_q={len(unresolved)}")
    for state in sorted(free)[:100]:
        print("FREE", state)
    for state in sorted(unresolved)[:100]:
        print("UNRESOLVED", state)
        print("POST_SATURATION", saturation_images[state])


if __name__ == "__main__":
    main()
