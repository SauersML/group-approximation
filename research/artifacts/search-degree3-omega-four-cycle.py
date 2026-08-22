#!/usr/bin/env python3
"""Exact ordered degree-three search for the Leavitt Omega four-cycle.

The sign screen is topology-first: retain precisely the cyclic covers with
one unary orbit and two trivalent residual orbits.  For each full seven-letter
Leavitt packet layout, solve the unary orbit for z in faithful Bergman normal
form.  If the quotient of the two ordered residual relators is conjugate to
the marked coefficient h=[c,d], then the two relators force h=1.
"""

import argparse
import importlib.util
from itertools import combinations, permutations
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)

PACKET = ("r", "e", "a", "c", "b", "d", "p")


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def orbit_word(slots, signs, start):
    height = start
    word = []
    for name, sign in zip(slots, signs):
        residue = height % 3
        quotient = (height - residue) // 3
        append_z(word, quotient)
        word.append(("g", residue, name, 1))
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


def inverse_unit(unit):
    return P.canon({(right, left) for left, right in unit})


def inverse_normal_form(word):
    return tuple((copy, inverse_unit(unit))
                 for copy, unit in reversed(word))


def reduce_units(factors):
    stack = []
    for copy, unit in factors:
        if unit == P.ONE:
            continue
        if stack and stack[-1][0] == copy:
            unit = P.mul(stack.pop()[1], unit)
            if unit == P.ONE:
                continue
        stack.append((copy, unit))
    return tuple(stack)


def cyclic_reduce(word):
    word = tuple(word)
    while len(word) > 1 and word[0][0] == word[-1][0]:
        first = word[0]
        last = word[-1]
        word = reduce_units(word[1:-1] + (
            (first[0], P.mul(last[1], first[1])),))
    return word


def unary_value(word):
    positions = [index for index, token in enumerate(word)
                 if token[0] == "z"]
    if len(positions) != 1:
        return None
    position = positions[0]
    rotated = word[position:] + word[:position]
    corner = P.reduce_free_product(tuple(token[1:]
                                         for token in rotated[1:]))
    return inverse_normal_form(corner) if rotated[0][1] == 1 else corner


def substitute(word, z_value):
    factors = []
    for token in word:
        if token[0] == "z":
            factors.extend(z_value if token[1] == 1
                           else inverse_normal_form(z_value))
        else:
            copy, name, exponent = token[1:]
            unit = P.UNITS[name] if exponent == 1 else P.INVERSES[name]
            factors.append((copy, unit))
    return reduce_units(tuple(factors))


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, default=0)
parser.add_argument("--shards", type=int, default=1)
args = parser.parse_args()
assert 0 <= args.shard < args.shards

topologies = []
for negative in combinations(range(7), 2):
    signs = tuple(-1 if index in negative else 1 for index in range(7))
    sample = tuple(orbit_word(PACKET, signs, start) for start in range(3))
    valences = tuple(sum(token[0] == "z" for token in word)
                     for word in sample)
    if sorted(valences) == [1, 3, 3]:
        topologies.append((negative, signs, valences))

assert len(topologies) == 14
tested = 0
for topology_index, (negative, signs, valences) in enumerate(topologies):
    if topology_index % args.shards != args.shard:
        continue
    pivot = valences.index(1)
    residual = tuple(index for index in range(3) if index != pivot)
    for slots in permutations(PACKET):
        tested += 1
        words = tuple(orbit_word(slots, signs, start) for start in range(3))
        z_value = unary_value(words[pivot])
        assert z_value is not None
        relations = tuple(substitute(words[index], z_value)
                          for index in residual)
        difference = cyclic_reduce(reduce_units(
            relations[1] + inverse_normal_form(relations[0])))
        if (len(difference) == 1 and
                difference[0][1] in (P.TARGET, P.TARGET_INV)):
            print("HIT", "negative", negative, "signs", signs,
                  "slots", slots, "pivot", pivot, "residual", residual,
                  "z_value", z_value, "relations", relations,
                  "difference_copy", difference[0][0], flush=True)
            raise SystemExit(42)

print("topologies", len(topologies))
print("tested", tested)
print("hits 0")
print("shard", args.shard, args.shards)
