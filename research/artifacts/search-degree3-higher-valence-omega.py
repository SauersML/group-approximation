#!/usr/bin/env python3
"""Search the degree-three (1,5,7) skeleton over the marked C2 gate.

This is a symbolic compound-block screen, not a packet permutation screen.
Each of the thirteen coefficient blocks is either 1 or the explicit Leavitt
gate h=[c,d].  The unary lift is solved exactly and the quotient of the two
ordered residual relators is tested for a conjugate of h.  A hit supplies a
bare gate skeleton into which neutral generator-carrying compounds can later
be inserted.
"""

import argparse
from itertools import combinations


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def orbit_word(mask, signs, start):
    height = start
    word = []
    for slot, sign in enumerate(signs):
        residue = height % 3
        quotient = (height - residue) // 3
        append_z(word, quotient)
        if mask & (1 << slot):
            word.append(("g", residue))
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
    # The explicit gate h=[c,d] is an involution, so inversion only reverses
    # the free-product syllables.
    return tuple(reversed(word))


def reduce_units(factors):
    stack = []
    for copy in factors:
        if stack and stack[-1] == copy:
            stack.pop()
        else:
            stack.append(copy)
    return tuple(stack)


def cyclic_reduce(word):
    word = tuple(word)
    while len(word) > 1 and word[0] == word[-1]:
        word = word[1:-1]
    return word


def unary_value(word):
    positions = [index for index, token in enumerate(word)
                 if token[0] == "z"]
    if len(positions) != 1:
        return None
    position = positions[0]
    rotated = word[position:] + word[:position]
    corner = reduce_units(tuple(token[1] for token in rotated[1:]))
    return inverse(corner) if rotated[0][1] == 1 else corner


def substitute(word, z_value):
    factors = []
    for token in word:
        if token[0] == "z":
            factors.extend(z_value if token[1] == 1 else inverse(z_value))
        else:
            factors.append(token[1])
    return reduce_units(tuple(factors))


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, default=0)
parser.add_argument("--shards", type=int, default=1)
args = parser.parse_args()
assert 0 <= args.shard < args.shards

tested = 0
assigned_signs = 0
eligible_layouts = 0
for sign_index, negative in enumerate(combinations(range(13), 5)):
    if sign_index % args.shards != args.shard:
        continue
    assigned_signs += 1
    signs = tuple(-1 if index in negative else 1 for index in range(13))
    for mask in range(1, 1 << 13):
        tested += 1
        words = tuple(orbit_word(mask, signs, start) for start in range(3))
        valences = tuple(sum(token[0] == "z" for token in word)
                         for word in words)
        if sorted(valences) != [1, 5, 7]:
            continue
        eligible_layouts += 1
        pivot = valences.index(1)
        residual = tuple(index for index in range(3) if index != pivot)
        z_value = unary_value(words[pivot])
        assert z_value is not None
        relations = tuple(substitute(words[index], z_value)
                          for index in residual)
        difference = cyclic_reduce(reduce_units(
            relations[1] + inverse(relations[0])))
        if len(difference) == 1:
            slots = tuple("h" if mask & (1 << index) else "1"
                          for index in range(13))
            print("HIT", "negative", negative, "signs", signs,
                  "slots", slots, "pivot", pivot, "residual", residual,
                  "z_value", z_value, "relations", relations,
                  "difference_copy", difference[0], flush=True)
            raise SystemExit(42)

print("sign_paths", 1287)
print("assigned_signs", assigned_signs)
print("tested", tested)
print("eligible_layouts", eligible_layouts)
print("hits 0")
print("shard", args.shard, args.shards)
