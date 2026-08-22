#!/usr/bin/env python3
"""Rank every (1,3,3,5) degree-four length-twelve triangle embedding."""

from collections import Counter
from itertools import combinations, product
import argparse


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def corners(signs, start):
    height, raw = start, []
    for slot, sign in enumerate(signs):
        residue = height % 4
        quotient = (height - residue) // 4
        append_z(raw, quotient)
        raw.append(("g", residue, slot))
        append_z(raw, -quotient)
        height += sign
    append_z(raw, 1)
    expanded = []
    for token in raw:
        if token[0] == "z":
            expanded.extend(("z", 1 if token[1] > 0 else -1)
                            for _ in range(abs(token[1])))
        else:
            expanded.append(token)
    cut = next(index for index, token in enumerate(expanded)
               if token[0] == "z")
    expanded = expanded[cut:] + expanded[:cut]
    result, index = [], 0
    while index < len(expanded):
        sign = expanded[index][1]
        index += 1
        corner = []
        while index < len(expanded) and expanded[index][0] != "z":
            _, copy, slot = expanded[index]
            corner.append((copy, slot))
            index += 1
        result.append((sign, tuple(corner)))
    return tuple(result)


def canonical(signs):
    variants = []
    for word in (signs, tuple(reversed(signs))):
        variants.extend(word[offset:] + word[:offset]
                        for offset in range(len(word)))
    return min(variants)


def orientation(triple, inverse, rotation):
    word = (tuple(reversed(tuple((name, -sign) for name, sign in triple)))
            if inverse else triple)
    return word[rotation:] + word[:rotation]


ORIENTATIONS = tuple((inverse, rotation) for inverse in (False, True)
                     for rotation in range(3))
TARGETS = (((0, 1), (1, 1), (2, 1)),
           ((2, -1), (3, 1), (4, 1)),
           ((4, -1), (5, 1), (0, -1)))


def embeddings(triple, valence):
    result = []
    for inverse, rotation in ORIENTATIONS:
        oriented = orientation(triple, inverse, rotation)
        if valence == 3:
            result.append(tuple(((index,), target)
                                for index, target in enumerate(oriented)))
            continue
        # All ordered cyclic contiguous partitions of five atoms into three
        # nonempty arcs: five starts times the six positive compositions.
        for start in range(5):
            for first in range(1, 4):
                for second in range(1, 5 - first):
                    third = 5 - first - second
                    if third < 1:
                        continue
                    sizes = (first, second, third)
                    cursor, groups = start, []
                    for size, target in zip(sizes, oriented):
                        indices = tuple((cursor + offset) % 5
                                        for offset in range(size))
                        groups.append((indices, target))
                        cursor += size
                    result.append(tuple(groups))
    return tuple(result)


def rank(matrix, prime=1_000_003):
    matrix = [[entry % prime for entry in row] for row in matrix]
    row = 0
    for column in range(len(matrix[0])):
        pivot = next((index for index in range(row, len(matrix))
                      if matrix[index][column]), None)
        if pivot is None:
            continue
        matrix[row], matrix[pivot] = matrix[pivot], matrix[row]
        scale = pow(matrix[row][column], prime - 2, prime)
        matrix[row] = [(entry * scale) % prime for entry in matrix[row]]
        for index in range(len(matrix)):
            if index != row and matrix[index][column]:
                scale = matrix[index][column]
                matrix[index] = [(left - scale * right) % prime
                                 for left, right in zip(matrix[index],
                                                        matrix[row])]
        row += 1
    return row


profiles = {}
for negative in combinations(range(12), 4):
    signs = tuple(-1 if index in negative else 1 for index in range(12))
    data = tuple(corners(signs, start) for start in range(4))
    if sorted(map(len, data)) == [1, 3, 3, 5]:
        profiles.setdefault(canonical(signs), signs)

parser = argparse.ArgumentParser()
parser.add_argument("--profile", help="restrict to one +- sign representative")
args = parser.parse_args()

global_best, winners = 100, []
for representative in sorted(profiles):
    text_profile = "".join("+" if sign > 0 else "-"
                           for sign in representative)
    if args.profile and text_profile != args.profile:
        continue
    data = tuple(corners(representative, start) for start in range(4))
    pivot_index = next(index for index, face in enumerate(data)
                       if len(face) == 1)
    pivot_sign, pivot_corner = data[pivot_index][0]
    faces = tuple(face for index, face in enumerate(data)
                  if index != pivot_index)
    # Put the five-valent orbit last and retain cyclic order among equal faces.
    faces = tuple(sorted(faces, key=len))
    choices = tuple(embeddings(TARGETS[index], len(face))
                    for index, face in enumerate(faces))
    counts, local_best, local_winners = Counter(), 100, []
    for selected in product(*choices):
        rows = []
        for face, grouping in zip(faces, selected):
            for indices, target in grouping:
                for copy in range(4):
                    row = [0] * 36
                    for index in indices:
                        stable_sign, corner = face[index]
                        hsign = -stable_sign * pivot_sign
                        for corner_copy, slot in pivot_corner:
                            if corner_copy == copy:
                                row[slot] += hsign
                        for corner_copy, slot in corner:
                            if corner_copy == copy:
                                row[slot] += 1
                    name, sign = target
                    row[12 + 4 * name + copy] -= sign
                    rows.append(row)
        for copy in range(4):
            row = [0] * 36
            for name in (1, 3, 5):
                row[12 + 4 * name + copy] += 1
            rows.append(row)
        constraint = rank(rows) - rank([row[12:] for row in rows])
        counts[constraint] += 1
        if constraint < local_best:
            local_best = constraint
            local_winners = [selected]
        elif constraint == local_best:
            local_winners.append(selected)
        if constraint < global_best:
            global_best, winners = constraint, [(representative, selected)]
        elif constraint == global_best:
            winners.append((representative, selected))
    print("profile", "".join("+" if sign > 0 else "-"
                              for sign in representative),
          "valences", tuple(map(len, data)), "rank_counts", dict(counts),
          "best", local_best, flush=True)
    for selected in local_winners:
        print("LOCAL_WIN", text_profile, selected, flush=True)

print("global_best", global_best, "winner_count", len(winners))
for representative, selected in winners[:40]:
    print("WIN", "".join("+" if sign > 0 else "-"
                          for sign in representative), selected)
