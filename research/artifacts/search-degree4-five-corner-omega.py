#!/usr/bin/env python3
"""Exact packet screen for the degree-four five-corner Omega compiler.

Only the two dihedral sign classes whose two residual orbits both have corner
lengths (1,1,1,1,8) are tested.  A sparse adaptive packet (repetitions
allowed) is injected into the slots.  A hit must pass the complete ordered
post-pivot test in faithful Bergman normal form: the second unary relator
vanishes and the quotient of the two residual relators is any nonidentity
one-copy word.
"""

import argparse
import importlib.util
from itertools import combinations, product
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)

def multiply(*units):
    result = P.ONE
    for unit in units:
        result = P.mul(result, unit)
    return result


u, v, v_inverse = multiply(P.A, P.B), multiply(P.C, P.D), multiply(P.D, P.C)
PAIRS = {
    "1": (P.ONE, P.ONE), "h": (P.TARGET, P.TARGET_INV),
    "u": (u, multiply(P.B, P.A)), "v": (v, v_inverse),
    "v-": (v_inverse, v), "a": (P.A, P.A), "b": (P.B, P.B),
    "c": (P.C, P.C), "d": (P.D, P.D), "e": (P.E, P.E),
    "r": (P.R, P.RINV), "p": (P.P, P.PINV),
}
NONIDENTITY = tuple(name for name in PAIRS if name != "1")
TOPOLOGIES = ("-+-++-+-++++", "-+-+++-+-+++")


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def orbit_word(slots, signs, start):
    height = start
    word = []
    for name, sign in zip(slots, signs):
        residue = height % 4
        quotient = (height - residue) // 4
        append_z(word, quotient)
        if name != "1":
            word.append(("g", residue, PAIRS[name]))
        append_z(word, -quotient)
        height += sign
    append_z(word, 1)
    expanded = []
    for token in word:
        if token[0] == "z":
            step = 1 if token[1] > 0 else -1
            expanded.extend(("z", step) for _ in range(abs(token[1])))
        else:
            expanded.append(token)
    return tuple(expanded)


def multiply_pair(left, right):
    return (P.mul(left[0], right[0]), P.mul(right[1], left[1]))


def inverse_normal_form(word):
    return tuple((copy, (pair[1], pair[0]))
                 for copy, pair in reversed(word))


def reduce_units(factors):
    stack = []
    for copy, pair in factors:
        if pair[0] == P.ONE:
            continue
        if stack and stack[-1][0] == copy:
            pair = multiply_pair(stack.pop()[1], pair)
            if pair[0] == P.ONE:
                continue
        stack.append((copy, pair))
    return tuple(stack)


def cyclic_reduce(word):
    word = tuple(word)
    while len(word) > 1 and word[0][0] == word[-1][0]:
        first = word[0]
        last = word[-1]
        word = reduce_units(word[1:-1] + (
            (first[0], multiply_pair(last[1], first[1])),))
    return word


def unary_value(word):
    positions = [index for index, token in enumerate(word)
                 if token[0] == "z"]
    if len(positions) != 1:
        return None
    position = positions[0]
    rotated = word[position:] + word[:position]
    corner = reduce_units(token[1:] for token in rotated[1:])
    return inverse_normal_form(corner) if rotated[0][1] == 1 else corner


def substitute(word, z_value):
    factors = []
    for token in word:
        if token[0] == "z":
            factors.extend(z_value if token[1] == 1
                           else inverse_normal_form(z_value))
        else:
            factors.append(token[1:])
    return reduce_units(factors)


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, default=0)
parser.add_argument("--shards", type=int, default=1)
parser.add_argument("--support", type=int, choices=range(1, 8), default=4)
args = parser.parse_args()
assert 0 <= args.shard < args.shards

tested = 0
for topology_index, topology in enumerate(TOPOLOGIES):
    signs = tuple(1 if sign == "+" else -1 for sign in topology)
    sample = tuple(orbit_word(("a",) * 12, signs, start)
                   for start in range(4))
    valences = tuple(sum(token[0] == "z" for token in word)
                     for word in sample)
    assert sorted(valences) == [1, 1, 5, 5]
    unary = tuple(index for index, value in enumerate(valences) if value == 1)
    residual = tuple(index for index, value in enumerate(valences)
                     if value == 5)

    layouts = ((positions, names) for positions in
               combinations(range(12), args.support)
               for names in product(NONIDENTITY, repeat=args.support))
    for layout_index, (positions, names) in enumerate(layouts):
        if (layout_index + topology_index) % args.shards != args.shard:
            continue
        if layout_index % (1000 * args.shards) < args.shards:
            P.mul.cache_clear()
        slots = ["1"] * 12
        for position, name in zip(positions, names):
            slots[position] = name
        words = tuple(orbit_word(slots, signs, start)
                      for start in range(4))
        for pivot, other in (unary, tuple(reversed(unary))):
            z_value = unary_value(words[pivot])
            if z_value is None:
                continue
            other_relation = substitute(words[other], z_value)
            if other_relation:
                continue
            relations = tuple(substitute(words[index], z_value)
                              for index in residual)
            difference = cyclic_reduce(reduce_units(
                relations[1] + inverse_normal_form(relations[0])))
            tested += 1
            if len(difference) == 1 and difference[0][1][0] != P.ONE:
                print("HIT", "topology", topology, "slots", tuple(slots),
                      "pivot", pivot, "residual", residual,
                      "z_value", z_value, "relations", relations,
                      "difference_copy", difference[0][0],
                      "mark_terms", len(difference[0][1][0]), flush=True)
                raise SystemExit(42)

print("ordered_candidates_tested", tested)
print("hits 0")
print("shard", args.shard, args.shards)
