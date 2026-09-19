#!/usr/bin/env python3
"""True-inverse replay of the degree-three ordered Leavitt screens.

Unlike the retired screen, this program never takes the transpose of a
Bergman chart element.  Words and their inverses remain symbolic until the
last free-product reduction, where the explicit ``UNITS`` and ``INVERSES``
tables are used.  Both inverse identities are checked before enumeration.
"""

import argparse
import importlib.util
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)

# Compound order-mismatch gates used by the length-nine replay.
P.UNITS["u"] = P.mul(P.A, P.B)
P.INVERSES["u"] = P.UNITS["u"]
P.UNITS["v"] = P.mul(P.C, P.D)
P.INVERSES["v"] = P.mul(P.D, P.C)
assert P.mul(P.UNITS["u"], P.INVERSES["u"]) == P.ONE
assert P.mul(P.UNITS["v"], P.INVERSES["v"]) == P.ONE

DEFAULT_PACKET = ("r", "e", "a", "c", "b", "d", "p")


def check_generator_inverses():
    assert set(P.UNITS) == set(P.INVERSES)
    for name, forward in P.UNITS.items():
        backward = P.INVERSES[name]
        assert P.mul(forward, backward) == P.ONE
        assert P.mul(backward, forward) == P.ONE


def multiset_permutations(values):
    counts = Counter(values)
    names = tuple(counts)
    result = [None] * len(values)

    def visit(position):
        if position == len(result):
            yield tuple(result)
            return
        for name in names:
            if counts[name]:
                counts[name] -= 1
                result[position] = name
                yield from visit(position + 1)
                counts[name] += 1

    yield from visit(0)


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


def inverse_symbolic(word):
    return tuple((copy, name, -exponent)
                 for copy, name, exponent in reversed(word))


def unary_value(word):
    positions = [index for index, token in enumerate(word)
                 if token[0] == "z"]
    assert len(positions) == 1
    position = positions[0]
    rotated = word[position:] + word[:position]
    corner = tuple(token[1:] for token in rotated[1:])
    return inverse_symbolic(corner) if rotated[0][1] == 1 else corner


def substitute_symbolic(word, z_value):
    factors = []
    for token in word:
        if token[0] == "z":
            factors.extend(z_value if token[1] == 1
                           else inverse_symbolic(z_value))
        else:
            factors.append(token[1:])
    return tuple(factors)


def reduce_units(factors):
    """Reduce already evaluated ``(copy, chart)`` factors."""
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


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, required=True)
parser.add_argument("--shards", type=int, required=True)
parser.add_argument("--packet", default=",".join(DEFAULT_PACKET))
parser.add_argument("--length", type=int, default=7, choices=(7, 9))
args = parser.parse_args()
assert 0 <= args.shard < args.shards
packet = tuple(args.packet.split(","))
assert len(packet) == args.length and all(name in P.UNITS for name in packet)

check_generator_inverses()
desired_valences = [1, 3, 3] if args.length == 7 else [1, 1, 7]
negative_count = (args.length - 3) // 2
topologies = []
for negative in combinations(range(args.length), negative_count):
    signs = tuple(-1 if index in negative else 1
                  for index in range(args.length))
    sample = tuple(orbit_word(packet, signs, start) for start in range(3))
    valences = tuple(sum(token[0] == "z" for token in word)
                     for word in sample)
    if sorted(valences) == desired_valences:
        topologies.append((negative, signs, valences))

assert len(topologies) == (14 if args.length == 7 else 9)
tested = 0
pivots = 0
for topology_index, (negative, signs, valences) in enumerate(topologies):
    if topology_index % args.shards != args.shard:
        continue
    unary = tuple(index for index, value in enumerate(valences) if value == 1)
    layouts = (permutations(packet) if len(set(packet)) == len(packet)
               else multiset_permutations(packet))
    for slots in layouts:
        tested += 1
        words = tuple(orbit_word(slots, signs, start) for start in range(3))
        for pivot in unary:
            pivots += 1
            z_value = unary_value(words[pivot])
            residual = tuple(index for index in range(3) if index != pivot)
            symbolic = tuple(substitute_symbolic(words[index], z_value)
                             for index in residual)
            if args.length == 7:
                difference = P.reduce_free_product(
                    symbolic[1] + inverse_symbolic(symbolic[0]))
                reduced = cyclic_reduce(difference)
                hit = (len(reduced) == 1 and
                       reduced[0][1] in (P.TARGET, P.TARGET_INV))
            else:
                other_unary = next(index for index in unary if index != pivot)
                other_position = residual.index(other_unary)
                target_position = 1 - other_position
                other = P.reduce_free_product(symbolic[other_position])
                reduced = cyclic_reduce(
                    P.reduce_free_product(symbolic[target_position]))
                hit = (not other and len(reduced) == 1 and
                       reduced[0][1] in (P.TARGET, P.TARGET_INV))
            if hit:
                print("HIT", "negative", negative, "signs", signs,
                      "slots", slots, "pivot", pivot,
                      "residual", residual, "reduced", reduced, flush=True)
                raise SystemExit(42)

print("length", args.length)
print("topologies", len(topologies))
print("layouts", tested, "pivots", pivots)
print("hits 0")
print("shard", args.shard, args.shards)
