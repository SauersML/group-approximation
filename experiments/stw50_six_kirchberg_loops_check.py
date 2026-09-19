#!/usr/bin/env python3
"""Exact finite certificate for stw50-six-kirchberg-loops-2026-09-05.md.

This checks integer lattices, graph-row supports, and graded tensor signs.
It does not prove any analytic C*-algebra theorem or classification input.
Run with Python 3; no third-party dependencies are required.
"""

from fractions import Fraction
from itertools import combinations


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def multiply(left, right):
    return [[sum(a * b for a, b in zip(row, col))
             for col in zip(*right)] for row in left]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def determinant(matrix):
    a = [[Fraction(v) for v in row] for row in matrix]
    result = Fraction(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        value = a[j][j]
        result *= value
        for i in range(j + 1, len(a)):
            ratio = a[i][j] / value
            for k in range(j, len(a)):
                a[i][k] -= ratio * a[j][k]
    assert result.denominator == 1
    return int(result)


def inverse(matrix):
    n = len(matrix)
    a = [[Fraction(v) for v in row + unit]
         for row, unit in zip(matrix, identity(n))]
    for j in range(n):
        pivot = next(i for i in range(j, n) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        value = a[j][j]
        a[j] = [v / value for v in a[j]]
        for i in range(n):
            if i != j:
                ratio = a[i][j]
                a[i] = [v - ratio * w for v, w in zip(a[i], a[j])]
    result = [row[n:] for row in a]
    assert all(v.denominator == 1 for row in result for v in row)
    return [[int(v) for v in row] for row in result]


def graph_certificate(u, expected_adjacency, quotient, quotient_basis):
    n = len(u)
    # Edge labels are (source, range, label); label 0 is distinguished.
    outgoing = []
    for i in range(n):
        outgoing.append({(i, j, k) for j in range(n)
                         for k in range(1, u[j] + 1)} | {(i, i, 0)})
    adjacency = [[sum(edge[1] == j for edge in outgoing[i])
                  for j in range(n)] for i in range(n)]
    assert adjacency == expected_adjacency
    boundary = [[int(i == j) - adjacency[j][i] for j in range(n)]
                for i in range(n)]
    assert boundary == [[-u[i]] * n for i in range(n)]
    assert min(u) > 0 and all(adjacency[i][i] >= 2 for i in range(n))

    # Certify the common initial-column projection and the row partition.
    slots = [(j, k) for j in range(n) for k in range(1, u[j] + 2)]
    for i in range(n):
        entries = []
        for j, k in slots:
            if k <= u[j]:
                entries.append(("edge", (i, j, k)))
            elif j == i:
                entries.append(("edge", (i, i, 0)))
            else:
                entries.append(("vertex", j))
        assert {entry for kind, entry in entries if kind == "edge"} == outgoing[i]
        assert {entry for kind, entry in entries if kind == "vertex"} == set(range(n)) - {i}
        initials = [entry[1] if kind == "edge" else entry for kind, entry in entries]
        assert initials == [j for j, _ in slots]
        for (kind_a, a), (kind_b, b) in combinations(entries, 2):
            if kind_a == kind_b:
                assert a != b  # Distinct edges or distinct vertices.
            else:
                edge = a if kind_a == "edge" else b
                vertex = b if kind_b == "vertex" else a
                assert edge[0] != vertex

    # The relation vector plus the proposed quotient basis is unimodular.
    lattice = transpose([list(u)] + quotient_basis)
    assert abs(determinant(lattice)) == 1
    assert multiply(quotient, transpose([list(u)])) == [[0] for _ in quotient]
    assert multiply(quotient, transpose(quotient_basis)) == identity(n - 1)
    assert multiply(quotient, [[1] for _ in u]) == [[1]] + [[0]] * (n - 2)
    # The boundary kernel has the standard difference vectors as a basis:
    # boundary(v)=0 iff sum(v)=0 because u is nonzero.
    differences = [[int(j == i) - int(j == n - 1) for j in range(n)]
                   for i in range(n - 1)]
    assert multiply(boundary, transpose(differences)) == [[0] * (n - 1) for _ in u]
    return quotient


def main():
    q_c = graph_certificate(
        (1, 1, 2), [[2, 1, 2], [1, 2, 2], [1, 1, 3]],
        [[0, 2, -1], [1, -1, 0]], [[1, 1, 1], [1, 0, 0]],
    )
    q_b = graph_certificate(
        (1, 2), [[2, 2], [1, 3]], [[2, -1]], [[1, 1]],
    )
    assert -q_b[0][1] == 1  # Inverse phase on a_12 sends [V] to [1].

    # Four edge actions: (source, range, winding), zero-based vertices.
    edge_actions = [(0, 2, -1), (0, 0, 1), (1, 2, -1), (1, 0, 1)]
    columns = []
    for source, target, winding in edge_actions:
        col = [0] * 6
        col[2 * source] = winding * q_c[0][target]
        col[2 * source + 1] = winding * q_c[1][target]
        columns.append(col)
    assert transpose(columns)[:4] == identity(4)

    # Tensor bases are e=(0,0), beta=(1,1), x=(1,0), y=(0,1).
    # Gamma's reduced map changes v (1) to e_B (0); moving the odd
    # circle coefficient before earlier factors contributes the sign.
    coordinates = [((1, 0), (0, 0)), ((1, 0), (1, 1)),
                   ((0, 1), (0, 0)), ((0, 1), (1, 1)),
                   ((1, 1), (1, 0)), ((1, 1), (0, 1))]
    for factor in (0, 1):
        col = []
        for domain, codomain in coordinates:
            image = list(domain)
            image[factor] = 0
            coefficient = ((-1) ** sum(domain[:factor])
                           if domain[factor] and tuple(image) == codomain else 0)
            col.append(coefficient)
        columns.append(col)

    matrix = transpose(columns)
    expected = [[1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0],
                [0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0],
                [0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 1, 0]]
    assert matrix == expected
    assert determinant(matrix) == 1
    inv = inverse(matrix)
    assert multiply(matrix, inv) == multiply(inv, matrix) == identity(6)
    assert inv == [[1, 0, 0, 0, 0, -1], [0, 1, 0, 0, 0, 0],
                   [0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 0, 0],
                   [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0]]

    subtract = lambda a, b: [v - w for v, w in zip(a, b)]
    kernel = transpose([columns[1], columns[3],
                        subtract(columns[4], columns[0]),
                        subtract(columns[5], columns[2])])
    assert kernel[0] == kernel[2] == [0] * 4
    assert abs(determinant([kernel[i] for i in (1, 3, 4, 5)])) == 1

    print("PASS: both finite graph-row and scaled K-lattice certificates")
    print("PASS: four edge-action columns and both graded tensor-action columns")
    print("PASS: six-loop determinant = 1; exact integer inverse verified")
    print("PASS: four-loop kernel basis is unimodular in the kernel lattice")
    print("Scope: finite algebraic checks only; analytic inputs are cited in the proof.")


if __name__ == "__main__":
    main()
