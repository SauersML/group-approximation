#!/usr/bin/env python3
"""True-inverse replay of the degree-four full-packet unary screen.

The two minimal five-corner sign classes are independent shards.  Every
inverse remains a symbolic word until evaluation in the faithful Bergman
chart, whose generator inverse table is checked two-sidedly first.
"""

import argparse
import importlib.util
from collections import Counter
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)

PACKET = ("r", "e", "a", "c", "b", "d", "p",
          "1", "1", "1", "1", "1")
TOPOLOGIES = ("-+-++-+-++++", "-+-+++-+-+++")


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
        residue = height % 4
        quotient = (height - residue) // 4
        append_z(word, quotient)
        if name != "1":
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


def substitute(word, z_value):
    factors = []
    for token in word:
        if token[0] == "z":
            factors.extend(z_value if token[1] == 1
                           else inverse_symbolic(z_value))
        else:
            factors.append(token[1:])
    return P.reduce_free_product(tuple(factors))


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, choices=range(2), required=True)
args = parser.parse_args()

check_generator_inverses()
topology = TOPOLOGIES[args.shard]
signs = tuple(1 if sign == "+" else -1 for sign in topology)
sample_words = tuple(orbit_word(("a",) * 12, signs, start)
                     for start in range(4))
valences = tuple(sum(token[0] == "z" for token in word)
                 for word in sample_words)
assert sorted(valences) == [1, 1, 5, 5]
unary_indices = tuple(index for index, value in enumerate(valences)
                      if value == 1)
assert len(unary_indices) == 2

layouts_tested = 0
pivots_tested = 0
compatible_pivots = 0
for slots in multiset_permutations(PACKET):
    layouts_tested += 1
    if layouts_tested % 10000 == 0:
        P.reduce_free_product.cache_clear()
    words = tuple(orbit_word(slots, signs, start) for start in range(4))
    for pivot, other in (unary_indices, tuple(reversed(unary_indices))):
        pivots_tested += 1
        other_relation = substitute(words[other], unary_value(words[pivot]))
        if not other_relation:
            compatible_pivots += 1
            print("HIT", "topology", topology, "slots", slots,
                  "pivot", pivot, "other", other, flush=True)
            raise SystemExit(42)

assert layouts_tested == 3991680
assert pivots_tested == 7983360
print("shard", args.shard, 2)
print("topology", topology)
print("layouts", layouts_tested, "pivots", pivots_tested)
print("compatible_pivots", compatible_pivots)
print("hits 0")
