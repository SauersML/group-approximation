#!/usr/bin/env python3
"""Exact true-inverse replay of the degree-three direct-pivot screen.

This verifier deliberately contains no operation that transposes a Bergman
chart.  Inverses remain symbolic words until ``reduce_free_product`` evaluates
each generator through the explicit ``UNITS``/``INVERSES`` tables.  The tables
are checked two-sidedly before the census starts.
"""

import argparse
import importlib.util
from collections import Counter
from itertools import combinations
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)

PACKET = ("r", "e", "a", "c", "1", "b", "d", "p", "1", "1", "1")


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


def topologies():
    result = []
    sample_slots = ("a",) * 11
    for negative in combinations(range(11), 4):
        signs = tuple(-1 if index in negative else 1
                      for index in range(11))
        words = tuple(orbit_word(sample_slots, signs, start)
                      for start in range(3))
        valences = tuple(sum(token[0] == "z" for token in word)
                         for word in words)
        if sorted(valences) == [1, 1, 9]:
            result.append((negative, signs, valences))
    return tuple(result)


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, required=True)
parser.add_argument("--shards", type=int, default=11)
args = parser.parse_args()
assert 0 <= args.shard < args.shards

check_generator_inverses()
all_topologies = topologies()
assert len(all_topologies) == 11

assigned_topologies = 0
layouts_tested = 0
pivots_tested = 0
for topology_index, (negative, signs, valences) in enumerate(all_topologies):
    if topology_index % args.shards != args.shard:
        continue
    assigned_topologies += 1
    target_index = valences.index(9)
    unary_indices = tuple(index for index in range(3)
                          if index != target_index)
    assert len(unary_indices) == 2
    for slots in multiset_permutations(PACKET):
        layouts_tested += 1
        # ``reduce_free_product`` is globally memoized by the shared chart
        # module.  The census visits millions of one-use words, so retaining
        # the whole cache only increases memory and cannot affect exactness.
        if layouts_tested % 10000 == 0:
            P.reduce_free_product.cache_clear()
        words = tuple(orbit_word(slots, signs, start)
                      for start in range(3))
        for unary_index in unary_indices:
            pivots_tested += 1
            reduced = substitute(words[target_index],
                                 unary_value(words[unary_index]))
            if (len(reduced) == 1 and
                    reduced[0][1] in (P.TARGET, P.TARGET_INV)):
                print("HIT", "negative", negative, "signs", signs,
                      "slots", slots, "pivot", unary_index,
                      "target", target_index, "copy", reduced[0][0],
                      flush=True)
                raise SystemExit(42)

expected_topologies = sum(index % args.shards == args.shard
                          for index in range(11))
assert assigned_topologies == expected_topologies
assert layouts_tested == assigned_topologies * 1663200
assert pivots_tested == 2 * layouts_tested
print("shard", args.shard, args.shards)
print("topologies", len(all_topologies), "assigned", assigned_topologies)
print("layouts", layouts_tested, "pivots", pivots_tested)
print("hits 0")
