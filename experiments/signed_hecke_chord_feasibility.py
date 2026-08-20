#!/usr/bin/env python3
"""Exact audits for the finite signed-Hecke chord feasibility criteria."""
from __future__ import annotations

import itertools
import json
from fractions import Fraction

Matrix = tuple[tuple[Fraction, ...], ...]


def multiply(left: Matrix, right: Matrix) -> Matrix:
    size = len(left)
    return tuple(
        tuple(sum((left[i][k] * right[k][j] for k in range(size)), Fraction())
              for j in range(size))
        for i in range(size)
    )


def subtract(left: Matrix, right: Matrix) -> Matrix:
    return tuple(tuple(a - b for a, b in zip(x, y)) for x, y in zip(left, right))


def commutator_equations(matrix: Matrix) -> list[list[Fraction]]:
    size = len(matrix)
    equations: list[list[Fraction]] = []
    for i in range(size):
        for j in range(size):
            row = [Fraction() for _ in range(size * size)]
            for k in range(size):
                row[i * size + k] += matrix[k][j]
                row[k * size + j] -= matrix[i][k]
            equations.append(row)
    return equations


def nullspace(rows: list[list[Fraction]], columns: int) -> list[list[Fraction]]:
    matrix = [row[:] for row in rows if any(row)]
    pivots: list[int] = []
    pivot_row = 0
    for column in range(columns):
        chosen = next((r for r in range(pivot_row, len(matrix)) if matrix[r][column]), None)
        if chosen is None:
            continue
        matrix[pivot_row], matrix[chosen] = matrix[chosen], matrix[pivot_row]
        scale = matrix[pivot_row][column]
        matrix[pivot_row] = [entry / scale for entry in matrix[pivot_row]]
        for r in range(len(matrix)):
            if r != pivot_row and matrix[r][column]:
                factor = matrix[r][column]
                matrix[r] = [a - factor * b for a, b in zip(matrix[r], matrix[pivot_row])]
        pivots.append(column)
        pivot_row += 1
        if pivot_row == len(matrix):
            break
    free = [column for column in range(columns) if column not in pivots]
    basis: list[list[Fraction]] = []
    for free_column in free:
        vector = [Fraction() for _ in range(columns)]
        vector[free_column] = Fraction(1)
        for r, pivot in enumerate(pivots):
            vector[pivot] = -matrix[r][free_column]
        basis.append(vector)
    return basis


def reshape(vector: list[Fraction], size: int) -> Matrix:
    return tuple(tuple(vector[i * size + j] for j in range(size)) for i in range(size))


def integer_transports(capacities: list[list[int]], rows: list[int], columns: list[int]) -> list[list[list[int]]]:
    bounds = [range(capacity + 1) for row in capacities for capacity in row]
    solutions: list[list[list[int]]] = []
    width = len(columns)
    for entries in itertools.product(*bounds):
        candidate = [list(entries[i * width:(i + 1) * width]) for i in range(len(rows))]
        if [sum(row) for row in candidate] != rows:
            continue
        if [sum(candidate[i][j] for i in range(len(rows))) for j in range(width)] != columns:
            continue
        solutions.append(candidate)
    return solutions


def matrix_as_ints(matrix: Matrix) -> list[list[int]]:
    return [[int(entry) for entry in row] for row in matrix]


def main() -> None:
    pauli_z: Matrix = ((Fraction(1), Fraction()), (Fraction(), Fraction(-1)))
    pauli_x: Matrix = ((Fraction(), Fraction(1)), (Fraction(1), Fraction()))
    common_basis = [
        reshape(vector, 2)
        for vector in nullspace(
            commutator_equations(pauli_z) + commutator_equations(pauli_x),
            4,
        )
    ]
    identity: Matrix = ((Fraction(1), Fraction()), (Fraction(), Fraction(1)))
    if common_basis != [identity]:
        raise AssertionError(common_basis)
    if subtract(multiply(pauli_z, pauli_x), multiply(pauli_x, pauli_z)) == ((0, 0), (0, 0)):
        raise AssertionError("Pauli separators unexpectedly commute")

    feasible_capacities = [[1, 1], [1, 1]]
    feasible = integer_transports(feasible_capacities, [1, 1], [1, 1])
    infeasible_capacities = [[1, 0], [0, 1]]
    infeasible = integer_transports(infeasible_capacities, [1, 1], [2, 0])
    if not feasible or infeasible:
        raise AssertionError((feasible, infeasible))

    print(json.dumps({
        "commuting_separator_transport": {
            "feasible_capacities": feasible_capacities,
            "feasible_demands": {"columns": [1, 1], "rows": [1, 1]},
            "feasible_solutions": feasible,
            "infeasible_capacities": infeasible_capacities,
            "infeasible_demands": {"columns": [2, 0], "rows": [1, 1]},
            "infeasible_solutions": infeasible,
        },
        "transverse_pauli_separator": {
            "common_commutant_basis": [matrix_as_ints(matrix) for matrix in common_basis],
            "common_involution_positive_ranks": [0, 2],
            "endpoint_positive_ranks": [1, 1],
            "regauging_feasible": False,
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
