#!/usr/bin/env python3
"""Exact GL(3,2) check for the minimal asymmetric three-block KL word."""

from itertools import product


def multiply(a, b):
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(3)) % 2 for j in range(3))
        for i in range(3)
    )


identity = tuple(tuple(int(i == j) for j in range(3)) for i in range(3))


def rank(a):
    rows = [list(row) for row in a]
    pivot = 0
    for column in range(3):
        selected = next((i for i in range(pivot, 3) if rows[i][column]), None)
        if selected is None:
            continue
        rows[pivot], rows[selected] = rows[selected], rows[pivot]
        for i in range(3):
            if i != pivot and rows[i][column]:
                rows[i] = [x ^ y for x, y in zip(rows[i], rows[pivot])]
        pivot += 1
    return pivot


group = []
for entries in product(range(2), repeat=9):
    matrix = tuple(tuple(entries[3 * i + j] for j in range(3)) for i in range(3))
    if rank(matrix) == 3:
        group.append(matrix)


def inverse(a):
    return next(b for b in group if multiply(a, b) == identity)


inverses = {a: inverse(a) for a in group}


def root(i, j):
    matrix = [list(row) for row in identity]
    matrix[i][j] = 1
    return tuple(tuple(row) for row in matrix)


r, s, v = root(0, 1), root(1, 2), root(2, 0)
patterns = {
    "++-": lambda t: (r, t, s, t, v, inverses[t]),
    "+-+": lambda t: (r, t, s, inverses[t], v, t),
    "-++": lambda t: (r, inverses[t], s, t, v, t),
}

assert len(group) == 168
for name, factors in patterns.items():
    solutions = []
    for t in group:
        value = identity
        for factor in factors(t):
            value = multiply(value, factor)
        if value == identity:
            solutions.append(t)
    assert not solutions, (name, solutions)

print("PASS: |GL(3,2)|=168 and all three asymmetric placements have no internal solution")

