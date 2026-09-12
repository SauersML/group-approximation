#!/usr/bin/env python3
"""True-inverse replay of the degree-three algebraic corner-cycle screen."""

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
LAYOUTS_PER_TOPOLOGY = 1663200


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


@lru_cache(maxsize=100000)
def reduce_named_corner(factors):
    return P.reduce_free_product(factors)


def signed_corner_symbolics(word):
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
        result.append((sign, tuple(factors)))
    return tuple(result)


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


def unary_form(corner_data):
    assert len(corner_data) == 1
    sign, symbolic = corner_data[0]
    return (sign,
            reduce_named_corner(symbolic),
            reduce_named_corner(inverse_symbolic(symbolic)))


def target_forms(corner_data):
    return tuple((sign, reduce_named_corner(symbolic))
                 for sign, symbolic in corner_data)


def two_pivot_target(pivot_data, other_data, target_data):
    pivot_sign, pivot, pivot_inverse = pivot_data
    other_sign, other, other_inverse = other_data
    assert pivot_sign == other_sign == 1
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
parser.add_argument("--shard", type=int, required=True)
parser.add_argument("--shards", type=int, default=11)
parser.add_argument("--offset", type=int, default=0)
parser.add_argument("--limit", type=int, default=0,
                    help="zero means no per-topology layout limit")
args = parser.parse_args()
assert 0 <= args.shard < args.shards
assert args.offset >= 0
assert args.limit >= 0

check_generator_inverses()
topologies = 0
assigned_topologies = 0
layouts_tested = 0
pivots_tested = 0
collision_pivots = 0
for negative in combinations(range(11), 4):
    signs = tuple(-1 if index in negative else 1 for index in range(11))
    sample = tuple(orbit_word(("a",) * 11, signs, start)
                   for start in range(3))
    valences = tuple(sum(token[0] == "z" for token in word)
                     for word in sample)
    if sorted(valences) != [1, 1, 9]:
        continue
    topology_index = topologies
    topologies += 1
    if topology_index % args.shards != args.shard:
        continue
    assigned_topologies += 1
    target_index = valences.index(9)
    unary_indices = tuple(index for index in range(3)
                          if index != target_index)
    sample_target_data = signed_corner_symbolics(sample[target_index])
    assert sorted(len(symbolic) for _, symbolic in sample_target_data) == (
        [1] * 8 + [3])

    for layout_index, slots in enumerate(multiset_permutations(PACKET)):
        if layout_index < args.offset:
            continue
        if args.limit and layout_index >= args.offset + args.limit:
            break
        layouts_tested += 1
        if layouts_tested % 10000 == 0:
            reduce_named_corner.cache_clear()
            P.reduce_free_product.cache_clear()
        words = tuple(orbit_word(slots, signs, start) for start in range(3))
        corner_data = tuple(signed_corner_symbolics(word) for word in words)
        assert all(sum(sign for sign, _ in data) == 1
                   for data in corner_data)
        assert all(sum(len(symbolic) for _, symbolic in data) == 7
                   for data in corner_data)
        assert all(len(corner_data[index]) == 1 and
                   corner_data[index][0][0] == 1
                   for index in unary_indices)
        unary_data = {
            index: unary_form(corner_data[index]) for index in unary_indices
        }
        target_symbolics = corner_data[target_index]
        collision_labels = {
            form for index in unary_indices for form in unary_data[index][1:]
        }
        # The all-nonidentity formal word has one triple target corner, but
        # deleting an identity coefficient can join (or cancel) neighbouring
        # z-powers.  Thus neither its reduced index nor its being the sole
        # possible algebraic collision is layout-invariant.  The formal
        # peeling theorem permits a skip exactly when *every* actual reduced
        # target corner avoids H,H^-1,Y,Y^-1.
        collision = False
        for _, symbolic in target_symbolics:
            if reduce_named_corner(symbolic) in collision_labels:
                collision = True
                break
        if not collision:
            pivots_tested += 2
            continue
        target_data = target_forms(target_symbolics)
        for pivot_index, other_index in (
                (unary_indices[0], unary_indices[1]),
                (unary_indices[1], unary_indices[0])):
            pivots_tested += 1
            reduced = two_pivot_target(
                unary_data[pivot_index], unary_data[other_index], target_data)
            collision_pivots += 1
            cyclic = cyclic_reduce(reduced)
            if (len(cyclic) == 1 and
                    cyclic[0][1] in (P.TARGET, P.TARGET_INV)):
                print("HIT", "negative", negative, "signs", signs,
                      "slots", slots, "pivot", pivot_index,
                      "other", other_index, "target", target_index,
                      "copy", cyclic[0][0], flush=True)
                raise SystemExit(42)

assert topologies == 11
expected = sum(index % args.shards == args.shard for index in range(11))
assert assigned_topologies == expected
layouts_per_topology = (min(args.limit, max(
    0, LAYOUTS_PER_TOPOLOGY - args.offset)) if args.limit else max(
        0, LAYOUTS_PER_TOPOLOGY - args.offset))
assert layouts_tested == assigned_topologies * layouts_per_topology
assert pivots_tested == 2 * layouts_tested
print("shard", args.shard, args.shards)
print("topologies", topologies, "assigned", assigned_topologies)
print("layouts", layouts_tested, "pivots", pivots_tested)
print("collision_pivots", collision_pivots)
print("hits 0")
print("offset", args.offset, "limit", args.limit)
