#!/usr/bin/env python3
"""Find the first one-letter formal long-corner core in degree three.

Each coefficient slot is 1, x, or x^-1.  Equality is exact in the free
product of three infinite cyclic coefficient copies.  The search exhausts
lengths three and five, then records the first length-seven witness.
"""

from itertools import combinations, product


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def reduce_word(word):
    stack = []
    for copy, exponent in word:
        if stack and stack[-1][0] == copy:
            exponent += stack.pop()[1]
        if exponent:
            stack.append((copy, exponent))
    return tuple(stack)


def inverse(word):
    return tuple((copy, -exponent)
                 for copy, exponent in reversed(word))


def orbit(slots, signs, start):
    height = start
    word = []
    for exponent, sign in zip(slots, signs):
        residue = height % 3
        quotient = (height - residue) // 3
        append_z(word, quotient)
        if exponent:
            word.append(("g", residue, exponent))
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
    result = []
    index = 0
    while index < len(expanded):
        sign = expanded[index][1]
        index += 1
        corner = []
        while index < len(expanded) and expanded[index][0] != "z":
            corner.append(expanded[index][1:])
            index += 1
        result.append((sign, reduce_word(corner)))
    return tuple(result)


def core_witness(slots, signs):
    orbits = tuple(orbit(slots, signs, start) for start in range(3))
    unary = tuple(index for index, data in enumerate(orbits)
                  if len(data) == 1 and data[0][1])
    if len(unary) < 2:
        return None
    for left, right in combinations(unary, 2):
        first = orbits[left][0][1]
        second = orbits[right][0][1]
        for target, data in enumerate(orbits):
            if target in (left, right) or len(data) < 2:
                continue
            target_corners = tuple(corner for _, corner in data if corner)
            first_hits = [index for index, corner in enumerate(target_corners)
                          if corner in (first, inverse(first))]
            second_hits = [index for index, corner in enumerate(target_corners)
                           if corner in (second, inverse(second))]
            if any(i != j for i in first_hits for j in second_hits):
                return left, right, target, orbits
    return None


tested = {}
witness = None
for length in (3, 5, 7):
    count = 0
    negative_count = (length - 3) // 2
    for negative in combinations(range(length), negative_count):
        signs = tuple(-1 if index in negative else 1
                      for index in range(length))
        for slots in product((0, 1, -1), repeat=length):
            count += 1
            hit = core_witness(slots, signs)
            if hit is not None:
                witness = length, negative, signs, slots, hit
                break
        if witness is not None:
            break
    tested[length] = count
    if witness is not None:
        break

assert witness is not None
length, negative, signs, slots, hit = witness
assert length == 7
left, right, target, orbits = hit
assert signs == (-1, 1, 1, 1, 1, -1, 1)
assert slots == (0, 1, 1, 1, 0, -1, -1)
assert orbits[left][0][1] == ((2, 1),)
assert orbits[right][0][1] == ((0, 1),)
print("tested_before_first_hit", tested)
print("degree 3 length", length)
print("signs", signs)
print("slots", slots)
print("unary_orbits", left, right)
print("target_orbit", target)
for index, data in enumerate(orbits):
    print("orbit", index, data)
