#!/usr/bin/env python3
"""Rank all 6^3 oriented d4 triangle carrier systems over a large prime."""

from collections import Counter
from itertools import product


H = ((0, 7), (1, 8), (2, 9), (3, 0), (2, 1),
     (1, 2), (0, 3), (1, 4), (2, 5), (3, 6))
FACES = (
    (((3, 1), (2, 2), (1, 3), (2, 4), (3, 5)),
     ((0, 6), (1, 7), (2, 8), (3, 9)), ((0, 0),)),
    (((3, 2), (2, 3), (3, 4)),
     ((0, 5), (1, 6), (2, 7), (3, 8)),
     ((0, 9), (1, 0), (0, 1))),
    (((3, 3),), ((0, 4), (1, 5), (2, 6), (3, 7)),
     ((0, 8), (1, 9), (2, 0), (1, 1), (0, 2))),
)
# P,A,Q / Q^-1,B,R / R^-1,C,P^-1.
TARGETS = (((0, 1), (1, 1), (2, 1)),
           ((2, -1), (3, 1), (4, 1)),
           ((4, -1), (5, 1), (0, -1)))


def orientation(triple, inverse, rotation):
    out = (list(reversed([(name, -sign) for name, sign in triple]))
           if inverse else list(triple))
    return out[rotation:] + out[:rotation]


ORIENTATIONS = tuple((inverse, rotation) for inverse in (False, True)
                     for rotation in range(3))


def rank(matrix, prime=1_000_003):
    matrix = [[entry % prime for entry in row] for row in matrix]
    row = 0
    for column in range(len(matrix[0])):
        pivot = next((index for index in range(row, len(matrix))
                      if matrix[index][column]), None)
        if pivot is None:
            continue
        matrix[row], matrix[pivot] = matrix[pivot], matrix[row]
        inverse = pow(matrix[row][column], prime - 2, prime)
        matrix[row] = [(entry * inverse) % prime for entry in matrix[row]]
        for index in range(len(matrix)):
            if index != row and matrix[index][column]:
                scale = matrix[index][column]
                matrix[index] = [(left - scale * right) % prime
                                 for left, right in
                                 zip(matrix[index], matrix[row])]
        row += 1
    return row


def slot_vector(word, copy):
    out = [0] * 10
    for index, slot in word:
        if index == copy:
            out[slot] += 1
    return out


ranked = []
for choices in product(range(6), repeat=3):
    rows = []
    for face, choice in enumerate(choices):
        inverse, rotation = ORIENTATIONS[choice]
        target = orientation(TARGETS[face], inverse, rotation)
        for corner in range(3):
            for copy in range(4):
                row = [0] * 34
                hsign = 1 if corner == 0 else -1
                for index, value in enumerate(slot_vector(H, copy)):
                    row[index] += hsign * value
                for index, value in enumerate(
                        slot_vector(FACES[face][corner], copy)):
                    row[index] += value
                name, sign = target[corner]
                row[10 + 4 * name + copy] -= sign
                rows.append(row)
    # A+B+C has zero abelian projection (the desired mark is a commutator).
    for copy in range(4):
        row = [0] * 34
        for name in (1, 3, 5):
            row[10 + 4 * name + copy] += 1
        rows.append(row)
    full = rank(rows)
    abstract = rank([row[10:] for row in rows])
    ranked.append((full - abstract, choices))

counts = Counter(item[0] for item in ranked)
assert counts == {7: 2, 8: 5, 9: 3, 10: 206}
print("constraint_rank_counts", dict(sorted(counts.items())))
for constraint, choices in sorted(ranked):
    if constraint <= 9:
        print(constraint, choices,
              tuple(ORIENTATIONS[index] for index in choices))
