#!/usr/bin/env python3
"""Search sparse nonzero-degree layouts with a deliberately duplicated tail.

The coefficient multiset consists of a,b,c,d, repeated copies of x, and
identities.  All five named coefficients are treated as abstract involutions;
equality is tested in the free product of ``degree`` copies of their free
product.  This isolates sign/corner geometry before choosing a Leavitt packet
realization of x.
"""

import argparse
from itertools import combinations, permutations


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def orbit_word(slots, signs, start, degree):
    height = start
    word = []
    for name, sign in zip(slots, signs):
        residue = height % degree
        quotient = (height - residue) // degree
        append_z(word, quotient)
        if name != "1":
            word.append(("g", residue, name))
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


def corners(word):
    first = next(i for i, token in enumerate(word) if token[0] == "z")
    word = word[first:] + word[:first]
    out = []
    i = 0
    while i < len(word):
        i += 1
        corner = []
        while i < len(word) and word[i][0] != "z":
            corner.append((word[i][1], word[i][2]))
            i += 1
        out.append(tuple(corner))
    return tuple(out)


def reduce_corner(corner):
    stack = []
    for factor in corner:
        if stack and stack[-1] == factor:
            stack.pop()
        else:
            stack.append(factor)
    return tuple(stack)


def singleton(corner):
    reduced = reduce_corner(corner)
    if len(reduced) == 1 and reduced[0][1] in ("a", "b", "c", "d"):
        return reduced[0]
    return None


def layouts(length, x_count):
    positions = range(length)
    for x_positions in combinations(positions, x_count):
        remaining = [i for i in positions if i not in x_positions]
        for gate_positions in permutations(remaining, 4):
            slots = ["1"] * length
            for position in x_positions:
                slots[position] = "x"
            for position, gate in zip(gate_positions, ("a", "b", "c", "d")):
                slots[position] = gate
            yield tuple(slots)


parser = argparse.ArgumentParser()
parser.add_argument("--length", type=int, default=8)
parser.add_argument("--degree", type=int, default=4)
parser.add_argument("--x-count", type=int, default=2)
parser.add_argument("--shard", type=int, default=0)
parser.add_argument("--shards", type=int, default=1)
args = parser.parse_args()
assert 1 <= args.degree <= args.length
assert (args.length - args.degree) % 2 == 0
assert args.x_count + 4 <= args.length
assert 0 <= args.shard < args.shards
negative_count = (args.length - args.degree) // 2

tested = 0
hits = []
for sign_index, negative_positions in enumerate(combinations(
        range(args.length), negative_count)):
    if sign_index % args.shards != args.shard:
        continue
    signs = tuple(-1 if i in negative_positions else 1
                  for i in range(args.length))
    for slots in layouts(args.length, args.x_count):
        tested += 1
        orbit_corners = tuple(corners(orbit_word(
            slots, signs, start, args.degree)) for start in range(args.degree))
        unary = [(i, reduce_corner(cs[0])) for i, cs in enumerate(orbit_corners)
                 if len(cs) == 1 and reduce_corner(cs[0])]
        trivalent = [(i, cs) for i, cs in enumerate(orbit_corners)
                     if len(cs) == 3]
        unary_values = {value for _, value in unary}
        for selected in combinations(trivalent, 2):
            gates = []
            valid = True
            for _, cs in selected:
                tails = [j for j, corner in enumerate(cs)
                         if reduce_corner(corner) in unary_values]
                if len(tails) != 1:
                    valid = False
                    break
                other = [singleton(corner) for j, corner in enumerate(cs)
                         if j != tails[0]]
                if any(value is None for value in other):
                    valid = False
                    break
                gates.extend(other)
            if not valid:
                continue
            by_name = {name: copy for copy, name in gates}
            if (set(by_name) == {"a", "b", "c", "d"}
                    and by_name["a"] == by_name["b"]
                    and by_name["c"] == by_name["d"]):
                hit = (negative_positions, slots,
                       tuple(index for index, _ in unary),
                       tuple(index for index, _ in selected), gates)
                hits.append(hit)
                print("HIT", hit, flush=True)

print("tested", tested)
print("transport_hits", len(hits))
print("shard", args.shard, args.shards)
