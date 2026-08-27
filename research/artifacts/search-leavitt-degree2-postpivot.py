#!/usr/bin/env python3
"""Exact Leavitt realization search for the degree-two post-pivot template.

For each shortest sign topology with one unary and one valence-nine orbit, the
unary Reidemeister--Schreier relator is solved for ``z``.  The solution is
substituted literally into the other orbit and reduced in the faithful
20-leaf Bergman normal form for the free product of the two coefficient
copies.  We test whether the result is the central involution [c,d] in either
copy.
"""

import importlib.util
import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)

PACKET = ("r", "e", "a", "c", "1", "b", "d", "p", "1", "1")


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
        residue = height % 2
        quotient = (height - residue) // 2
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


def inverse(word):
    return tuple((copy, name, -exponent)
                 for copy, name, exponent in reversed(word))


def unary_data(word):
    z_positions = [i for i, token in enumerate(word) if token[0] == "z"]
    if len(z_positions) != 1:
        return None
    position = z_positions[0]
    rotated = word[position:] + word[:position]
    sign = rotated[0][1]
    corner = tuple(token[1:] for token in rotated[1:])
    # z H=1 gives z=H^-1; z^-1 H=1 gives z=H.
    return inverse(corner) if sign == 1 else corner


def substitute(word, z_value):
    factors = []
    for token in word:
        if token[0] == "z":
            factors.extend(z_value if token[1] == 1 else inverse(z_value))
        else:
            factors.append(token[1:])
    return P.reduce_free_product(tuple(factors))


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, default=0)
parser.add_argument("--shards", type=int, default=1)
args = parser.parse_args()
assert 0 <= args.shard < args.shards

tested = 0
hits = []
topology_index = 0
for negative in combinations(range(10), 4):
    signs = tuple(-1 if i in negative else 1 for i in range(10))
    # The valences depend only on signs; reject all but the shortest 1+9 split.
    sample = tuple(orbit_word(("a",) * 10, signs, start)
                   for start in range(2))
    valences = tuple(sum(token[0] == "z" for token in word)
                     for word in sample)
    if sorted(valences) != [1, 9]:
        continue
    if topology_index % args.shards != args.shard:
        topology_index += 1
        continue
    topology_index += 1
    unary_index = valences.index(1)
    target_index = 1 - unary_index
    for slots in multiset_permutations(PACKET):
        tested += 1
        words = tuple(orbit_word(slots, signs, start) for start in range(2))
        z_value = unary_data(words[unary_index])
        reduced = substitute(words[target_index], z_value)
        if (len(reduced) == 1 and reduced[0][1] in
                (P.TARGET, P.TARGET_INV)):
            hit = (negative, signs, slots, unary_index, target_index,
                   reduced[0][0])
            hits.append(hit)
            print("HIT", hit, flush=True)
            raise SystemExit

print("tested", tested)
print("hits", len(hits))
print("shard", args.shard, args.shards)
