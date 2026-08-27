#!/usr/bin/env python3
"""Classify degree-four sign words with two unary and two trivalent orbits.

This is a tiny topology-only Reidemeister--Schreier audit.  It retains the
coefficient-slot indices and their free-product copy, so the output can be
checked independently of any Leavitt normal-form implementation.
"""

from itertools import combinations


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def signed_corners(signs, start, degree=4):
    height = start
    word = []
    for slot, sign in enumerate(signs):
        residue = height % degree
        quotient = (height - residue) // degree
        append_z(word, quotient)
        word.append(("g", residue, slot))
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
    first = next(index for index, token in enumerate(expanded)
                 if token[0] == "z")
    expanded = expanded[first:] + expanded[:first]

    answer = []
    index = 0
    while index < len(expanded):
        sign = expanded[index][1]
        index += 1
        corner = []
        while index < len(expanded) and expanded[index][0] != "z":
            corner.append(expanded[index][1:])
            index += 1
        answer.append((sign, tuple(corner)))
    return tuple(answer)


def dihedral_representative(signs):
    variants = []
    for word in (signs, tuple(reversed(signs))):
        variants.extend(word[index:] + word[:index]
                        for index in range(len(word)))
    return min(variants)


hits = []
for length in range(4, 21, 2):
    negative_count = (length - 4) // 2
    if negative_count < 0:
        continue
    for negative in combinations(range(length), negative_count):
        signs = tuple(-1 if index in negative else 1
                      for index in range(length))
        orbits = tuple(signed_corners(signs, start) for start in range(4))
        if sorted(map(len, orbits)) == [1, 1, 3, 3]:
            hits.append((signs, orbits))

by_length = {}
classes = {}
for signs, orbits in hits:
    by_length[len(signs)] = by_length.get(len(signs), 0) + 1
    representative = dihedral_representative(signs)
    classes[representative] = classes.get(representative, 0) + 1

print("by_length", sorted(by_length.items()))
print("dihedral_classes")
for representative, count in sorted(classes.items()):
    print(count, "".join("+" if sign == 1 else "-"
                         for sign in representative))

assert by_length == {8: 20}
assert sorted(classes.values()) == [4, 8, 8]

