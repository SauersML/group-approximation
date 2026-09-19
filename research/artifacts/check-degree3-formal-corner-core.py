#!/usr/bin/env python3
"""Check the formal corner inventory of degree-3 length-11 cyclic covers.

The seven nonidentity coefficient slots are distinct free symbols and four
slots are identities.  This is deliberately topology-only: it proves that a
minimal two-edge long-corner cycle cannot arise by literal formal equality.
It does not identify words using special relations in the Leavitt group.
"""

from itertools import combinations


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def orbit_word(slots, signs, start):
    height = start
    word = []
    for slot, sign in zip(slots, signs):
        residue = height % 3
        quotient = (height - residue) // 3
        append_z(word, quotient)
        if slot is not None:
            word.append(("g", residue, slot))
        append_z(word, -quotient)
        height += sign
    append_z(word, 1)
    return tuple(word)


def corners(word):
    expanded = []
    for token in word:
        if token[0] == "z":
            step = 1 if token[1] > 0 else -1
            expanded.extend(("z", step) for _ in range(abs(token[1])))
        else:
            expanded.append(token)
    first = next(i for i, token in enumerate(expanded) if token[0] == "z")
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
        result.append((sign, tuple(corner)))
    return tuple(result)


topologies = 0
identity_layouts = 0
literal_cycles = 0
shape_counts = {}
for negative in combinations(range(11), 4):
    signs = tuple(-1 if index in negative else 1 for index in range(11))
    sample = tuple(corners(orbit_word(tuple(range(11)), signs, start))
                   for start in range(3))
    valences = tuple(len(orbit) for orbit in sample)
    if sorted(valences) != [1, 1, 9]:
        continue
    topologies += 1
    target_index = valences.index(9)
    unary_indices = tuple(index for index in range(3)
                          if index != target_index)
    sizes = tuple(sorted(len(corner) for _, corner in sample[target_index]))
    shape_counts[sizes] = shape_counts.get(sizes, 0) + 1
    for identities in combinations(range(11), 4):
        identity_layouts += 1
        slots = tuple(None if index in identities else index
                      for index in range(11))
        orbit_corners = tuple(corners(orbit_word(slots, signs, start))
                              for start in range(3))
        unary = tuple(orbit_corners[index][0][1]
                      for index in unary_indices)
        target = tuple(corner for _, corner in orbit_corners[target_index]
                       if corner)
        # A literal minimal four-incidence core requires both unary long words
        # (up to inversion) among the target corners.  Distinct free symbols
        # make ordinary tuple comparison a faithful normal-form comparison.
        target_oriented = set(target)
        target_oriented.update(tuple(reversed(corner)) for corner in target)
        if all(word in target_oriented or tuple(reversed(word)) in target_oriented
               for word in unary):
            literal_cycles += 1

assert topologies == 11
assert identity_layouts == 11 * 330
assert shape_counts == {(1, 1, 1, 1, 1, 1, 1, 1, 3): 11}
assert literal_cycles == 0
print("topologies", topologies)
print("identity_layouts", identity_layouts)
print("target_shapes", shape_counts)
print("literal_minimal_four_incidence_cycles", literal_cycles)
