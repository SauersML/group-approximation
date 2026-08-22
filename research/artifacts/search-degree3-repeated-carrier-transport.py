#!/usr/bin/env python3
"""Search a symbolic repeated-carrier degree-three transport compiler.

At length thirteen and exponent three, retain the (1,5,7) orbit topology.
Place the four involutory gates a,b,c,d at four cyclic sign changes and put
one repeated formal carrier x in every other coefficient slot.  After solving
the unary orbit, recognize the two ordered residual relators exactly as

    A U C U^-1,      B U D U^-1

up to cyclic rotation and simultaneous source/target swaps.  Reduction is in
the finer free product of the formal cyclic letter groups, so every reported
identity remains valid after specializing x to any Leavitt coefficient word.
"""

import argparse
from itertools import combinations, permutations


INVOLUTIONS = frozenset(("a", "b", "c", "d"))
GATES = ("a", "b", "c", "d")


def inverse_letter(letter):
    copy, name, exponent = letter
    return copy, name, exponent if name in INVOLUTIONS else -exponent


def inverse(word):
    return tuple(inverse_letter(letter) for letter in reversed(word))


def reduce_letters(word):
    stack = []
    for letter in word:
        copy, name, exponent = letter
        if name in INVOLUTIONS:
            exponent = 1
        letter = (copy, name, exponent)
        if (stack and stack[-1][0] == copy and
                stack[-1][1] == name and
                (name in INVOLUTIONS or stack[-1][2] == -exponent)):
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


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


def unary_value(word):
    positions = [index for index, token in enumerate(word)
                 if token[0] == "z"]
    if len(positions) != 1:
        return None
    position = positions[0]
    rotated = word[position:] + word[:position]
    corner = reduce_letters(tuple(token[1:] for token in rotated[1:]))
    return inverse(corner) if rotated[0][1] == 1 else corner


def substitute(word, z_value):
    factors = []
    for token in word:
        if token[0] == "z":
            factors.extend(z_value if token[1] == 1 else inverse(z_value))
        else:
            factors.append(token[1:])
    return reduce_letters(tuple(factors))


def transports(word):
    """Return (source,target,U) witnesses for A U C U^-1 rotations."""
    out = []
    for source_index, source in enumerate(word):
        if source[1] not in ("a", "b"):
            continue
        rotated = word[source_index:] + word[:source_index]
        for target_index in range(1, len(rotated)):
            target = rotated[target_index]
            if target[1] not in ("c", "d"):
                continue
            carrier = rotated[1:target_index]
            if rotated[target_index + 1:] != inverse(carrier):
                continue
            out.append((source[1], target[1], carrier,
                        source[0], target[0]))
    return tuple(out)


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, default=0)
parser.add_argument("--shards", type=int, default=1)
args = parser.parse_args()
assert 0 <= args.shard < args.shards

topologies = 0
tested = 0
for sign_index, negative in enumerate(combinations(range(13), 5)):
    signs = tuple(-1 if index in negative else 1 for index in range(13))
    sample = tuple(orbit_word(("x",) * 13, signs, start)
                   for start in range(3))
    valences = tuple(sum(token[0] == "z" for token in word)
                     for word in sample)
    if sorted(valences) != [1, 5, 7]:
        continue
    topology = topologies
    topologies += 1
    if topology % args.shards != args.shard:
        continue
    pivot = valences.index(1)
    residual = tuple(index for index in range(3) if index != pivot)
    changes = tuple(index for index in range(13)
                    if signs[index - 1] != signs[index])
    if len(changes) < 4:
        continue
    for gate_positions in combinations(changes, 4):
        for gate_order in permutations(GATES):
            slots = ["x"] * 13
            for position, gate in zip(gate_positions, gate_order):
                slots[position] = gate
            slots = tuple(slots)
            tested += 1
            words = tuple(orbit_word(slots, signs, start)
                          for start in range(3))
            z_value = unary_value(words[pivot])
            assert z_value is not None
            relations = tuple(substitute(words[index], z_value)
                              for index in residual)
            first = transports(relations[0])
            second = transports(relations[1])
            for left in first:
                for right in second:
                    complementary = ({left[0], right[0]} == {"a", "b"} and
                                     {left[1], right[1]} == {"c", "d"})
                    if complementary and left[2:] == right[2:]:
                        print("HIT", "negative", negative, "signs", signs,
                              "slots", slots, "pivot", pivot,
                              "residual", residual, "z_value", z_value,
                              "relations", relations,
                              "transports", (left, right), flush=True)
                        raise SystemExit(42)

print("topologies", topologies)
print("tested", tested)
print("hits 0")
print("shard", args.shard, args.shards)
