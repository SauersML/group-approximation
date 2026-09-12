#!/usr/bin/env python3
"""Exact full-packet search for degree-three 1+1+9 orbit topologies."""

import argparse
import importlib.util
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)

PACKET = ("r", "e", "a", "c", "1", "b", "d", "p", "1", "1", "1")


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


def inverse(word):
    return tuple((copy, name, -exponent)
                 for copy, name, exponent in reversed(word))


def unary_data(word):
    positions = [i for i, token in enumerate(word) if token[0] == "z"]
    if len(positions) != 1:
        return None
    position = positions[0]
    rotated = word[position:] + word[:position]
    corner = tuple(token[1:] for token in rotated[1:])
    return inverse(corner) if rotated[0][1] == 1 else corner


def signed_corner_normal_forms(word):
    first = next(index for index, token in enumerate(word)
                 if token[0] == "z")
    word = word[first:] + word[:first]
    result = []
    index = 0
    while index < len(word):
        sign = word[index][1]
        index += 1
        factors = []
        while index < len(word) and word[index][0] != "z":
            factors.append(word[index][1:])
            index += 1
        result.append((sign, reduce_named_corner(tuple(factors))))
    return tuple(result)


@lru_cache(maxsize=100000)
def reduce_named_corner(factors):
    return P.reduce_free_product(factors)


def substitute(word, z_value):
    factors = []
    for token in word:
        if token[0] == "z":
            factors.extend(z_value if token[1] == 1 else inverse(z_value))
        else:
            factors.append(token[1:])
    return P.reduce_free_product(tuple(factors))


def inverse_unit(unit):
    """Inverse in the faithful Bergman chart (transpose the monomials)."""
    return P.canon({(right, left) for left, right in unit})


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


def inverse_normal_form(word):
    return tuple((copy, inverse_unit(unit))
                 for copy, unit in reversed(word))


def multiply_normal_forms(left, right):
    return reduce_units(left + right)


def cyclic_reduce(word):
    word = tuple(word)
    while len(word) > 1 and word[0][0] == word[-1][0]:
        first = word[0]
        last = word[-1]
        word = reduce_units(word[1:-1] + (
            (first[0], P.mul(last[1], first[1])),))
    return word


def two_pivot_target(words, pivot_index, other_index, target_index):
    pivot_data = signed_corner_normal_forms(words[pivot_index])
    other_data = signed_corner_normal_forms(words[other_index])
    assert len(pivot_data) == len(other_data) == 1
    pivot_sign, pivot = pivot_data[0]
    other_sign, other = other_data[0]
    assert pivot_sign == other_sign == 1
    pivot_inverse = inverse_normal_form(pivot)
    other_inverse = inverse_normal_form(other)
    target_data = signed_corner_normal_forms(words[target_index])
    # By the formal two-core theorem, if the unique long target corner is
    # distinct from both unary corners in both orientations, it peels first
    # and D survives.  Only exact Leavitt collisions need target reduction.
    collision_labels = (pivot, pivot_inverse, other, other_inverse)
    if not any(corner in collision_labels for _, corner in target_data):
        return None
    factors = ()
    for sign, corner in target_data:
        factors = multiply_normal_forms(
            factors, pivot_inverse if sign == 1 else pivot)
        if corner == other:
            corner = pivot
        elif corner == other_inverse:
            corner = pivot_inverse
        factors = multiply_normal_forms(factors, corner)
    return factors


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, default=0)
parser.add_argument("--shards", type=int, default=1)
parser.add_argument("--offset", type=int, default=0)
parser.add_argument("--limit", type=int, default=0,
                    help="zero means no layout limit")
parser.add_argument("--mode", choices=("direct", "two_pivot"),
                    default="direct")
args = parser.parse_args()
assert 0 <= args.shard < args.shards

tested = 0
topologies = 0
assigned_topologies = 0
for negative in combinations(range(11), 4):
    signs = tuple(-1 if i in negative else 1 for i in range(11))
    sample = tuple(orbit_word(("a",) * 11, signs, start)
                   for start in range(3))
    valences = tuple(sum(token[0] == "z" for token in word)
                     for word in sample)
    if sorted(valences) != [1, 1, 9]:
        continue
    topology = topologies
    topologies += 1
    if topology % args.shards != args.shard:
        continue
    assigned_topologies += 1
    target_index = valences.index(9)
    unary_indices = [i for i in range(3) if i != target_index]
    for layout_index, slots in enumerate(multiset_permutations(PACKET)):
        if layout_index < args.offset:
            continue
        if args.limit and layout_index >= args.offset + args.limit:
            break
        tested += 1
        words = tuple(orbit_word(slots, signs, start) for start in range(3))
        if args.mode == "two_pivot":
            for pivot_index in unary_indices:
                other_index = next(index for index in unary_indices
                                   if index != pivot_index)
                reduced = two_pivot_target(
                    words, pivot_index, other_index, target_index)
                if reduced is None:
                    continue
                cyclic = cyclic_reduce(reduced)
                if (len(cyclic) == 1 and cyclic[0][1] in
                        (P.TARGET, P.TARGET_INV)):
                    print("HIT", "negative", negative, "signs", signs,
                          "slots", slots, "pivot", pivot_index,
                          "other", other_index, "target", target_index,
                          "copy", cyclic[0][0], "orbit_words", words,
                          flush=True)
                    raise SystemExit(42)
            continue
        for unary_index in unary_indices:
            z_value = unary_data(words[unary_index])
            if z_value is None:
                continue
            reduced = substitute(words[target_index], z_value)
            if args.mode == "direct" and (len(reduced) == 1 and
                    reduced[0][1] in (P.TARGET, P.TARGET_INV)):
                print("HIT", "negative", negative, "signs", signs,
                      "slots", slots, "pivot", unary_index,
                      "target", target_index, "copy", reduced[0][0],
                      flush=True)
                raise SystemExit(42)

print("topologies", topologies)
print("assigned_topologies", assigned_topologies)
print("tested", tested)
print("hits 0")
print("shard", args.shard, args.shards)
print("offset", args.offset, "limit", args.limit)
print("mode", args.mode)
