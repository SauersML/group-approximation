#!/usr/bin/env python3
"""Search for a common nondegenerate hyperplane in every radical chart.

For an alternating selector pencil A(x) and a fixed radical-chart direction
ell, the crossed product has extended commutator form

    B_ell(x) = [[A(x), ell], [ell^T, 0]].

Every B_ell(x) has a one-dimensional radical.  A fixed hyperplane ker(phi)
is nondegenerate in every sector exactly when phi is nonzero on every one of
those radical lines.  Over F_2 this is the linear system

    phi(r_x) = 1  for every Boolean assignment x.

If soluble, the corresponding fixed subgroup is a full matrix packet in
every sector, and both simple blocks of the crossed-product chart restrict to
the same packet type.  This is the finite algebra needed by a Morita reset.
"""
from __future__ import annotations

from itertools import product

from schur_clifford_rank_gate import BitTuple, eval_matrix, rank_f2
from s3_equivariant_radical_compiler import (
    hyperbolic_tensor,
    symmetric_border,
)


DIRECTIONS: tuple[BitTuple, ...] = ((1, 0), (0, 1), (1, 1))


def solve_f2(rows: list[list[int]], rhs: list[int]) -> list[int] | None:
    """Return one solution to rows*x=rhs, or None."""
    if not rows:
        return []
    augmented = [row[:] + [value] for row, value in zip(rows, rhs)]
    width = len(rows[0])
    pivot_columns: list[int] = []
    rank = 0
    for column in range(width):
        pivot = next(
            (index for index in range(rank, len(augmented)) if augmented[index][column]),
            None,
        )
        if pivot is None:
            continue
        augmented[rank], augmented[pivot] = augmented[pivot], augmented[rank]
        for index in range(len(augmented)):
            if index != rank and augmented[index][column]:
                augmented[index] = [
                    left ^ right
                    for left, right in zip(augmented[index], augmented[rank])
                ]
        pivot_columns.append(column)
        rank += 1
    if any(not any(row[:width]) and row[width] for row in augmented):
        return None
    solution = [0] * width
    for row, column in enumerate(pivot_columns):
        solution[column] = augmented[row][width]
    return solution


def nullspace_vector(matrix: list[list[int]]) -> list[int]:
    """Return the unique nonzero vector in a corank-one square matrix."""
    width = len(matrix)
    rows = [row[:] for row in matrix]
    pivot_columns: list[int] = []
    rank = 0
    for column in range(width):
        pivot = next((index for index in range(rank, width) if rows[index][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for index in range(width):
            if index != rank and rows[index][column]:
                rows[index] = [left ^ right for left, right in zip(rows[index], rows[rank])]
        pivot_columns.append(column)
        rank += 1
    assert rank == width - 1
    free = next(column for column in range(width) if column not in pivot_columns)
    vector = [0] * width
    vector[free] = 1
    for row, column in reversed(list(enumerate(pivot_columns))):
        vector[column] = sum(
            rows[row][other] * vector[other] for other in range(column + 1, width)
        ) & 1
    assert any(vector)
    assert all(sum(a * b for a, b in zip(row, vector)) % 2 == 0 for row in matrix)
    return vector


def chart_directions(
    size: int,
    supports: dict[BitTuple, tuple[int, int]],
    symmetric_size: int,
) -> tuple[list[int], list[int], list[int]]:
    """Global functionals restricting to the same dual basis on every hot radical."""
    first = [0] * size
    second = [0] * size
    for start, _ in supports.values():
        first[start] = 1
        second[symmetric_size + start] = 1
    return first, second, [left ^ right for left, right in zip(first, second)]


def extended_form(alternating: list[list[int]], functional: list[int]) -> list[list[int]]:
    size = len(alternating)
    return [
        row[:] + [functional[index]] for index, row in enumerate(alternating)
    ] + [functional[:] + [0]]


def hyperplane_basis(functional: list[int]) -> list[list[int]]:
    """Column basis of ker(functional)."""
    pivot = next(index for index, value in enumerate(functional) if value)
    basis = []
    for index in range(len(functional)):
        if index == pivot:
            continue
        vector = [0] * len(functional)
        vector[index] = 1
        vector[pivot] = functional[index]
        basis.append(vector)
    assert all(
        sum(left * right for left, right in zip(functional, vector)) % 2 == 0
        for vector in basis
    )
    return basis


def restricted_form(matrix: list[list[int]], basis: list[list[int]]) -> list[list[int]]:
    image = [
        [sum(entry * value for entry, value in zip(row, vector)) & 1 for row in matrix]
        for vector in basis
    ]
    return [
        [sum(left * right for left, right in zip(vector, image[column])) & 1 for column in range(len(basis))]
        for vector in basis
    ]


def audit_predicate(
    k: int,
    forbidden: list[BitTuple],
    *,
    verify_restriction: bool = False,
    report_witnesses: bool = False,
) -> bool:
    if not forbidden:
        return True
    symmetric, supports, _ = symmetric_border(k, forbidden)
    alternating_affine = hyperbolic_tensor(symmetric, k)
    size = len(alternating_affine)
    directions = chart_directions(size, supports, len(symmetric))
    witness_supports = []
    for functional in directions:
        radicals = []
        for assignment in product((0, 1), repeat=k):
            alternating = eval_matrix(alternating_affine, assignment)
            extended = extended_form(alternating, functional)
            assert rank_f2(extended) == size
            radicals.append(nullspace_vector(extended))
        phi = solve_f2(radicals, [1] * len(radicals))
        if phi is None:
            return False
        assert all(sum(a * b for a, b in zip(phi, radical)) & 1 for radical in radicals)
        witness_supports.append(tuple(index for index, value in enumerate(phi) if value))
        if verify_restriction:
            basis = hyperplane_basis(phi)
            for assignment in product((0, 1), repeat=k):
                alternating = eval_matrix(alternating_affine, assignment)
                extended = extended_form(alternating, functional)
                assert rank_f2(restricted_form(extended, basis)) == size
    if report_witnesses:
        print(f"  symplectic-hyperplane witnesses={tuple(witness_supports)}")
    return True


def exhaustive(max_k: int = 3) -> None:
    for k in range(1, max_k + 1):
        cube = list(product((0, 1), repeat=k))
        failures = []
        for mask in range(1 << len(cube)):
            forbidden = [
                assignment
                for index, assignment in enumerate(cube)
                if (mask >> index) & 1
            ]
            if not audit_predicate(k, forbidden):
                failures.append(mask)
        print(
            f"exhaustive k={k}: {len(cube) and (1 << len(cube))} predicates, "
            f"common-hyperplane failures={len(failures)}"
        )
        if failures:
            print("first failure masks:", failures[:16])


def audit_fanizza_menu() -> None:
    """Audit the fixed nonlinear predicates left by the Fanizza flattening."""
    predicates = {
        "C13/C14": (
            3,
            lambda value: value[2] == 1 and value[0] != value[1],
        ),
        "C17": (
            3,
            lambda value: value[0] != (value[1] & value[2]),
        ),
        "C18 child-guard": (
            3,
            lambda value: value == (1, 0, 1),
        ),
        "C18 four-bit residual": (
            4,
            lambda value: value == (1, 1, 1, 1),
        ),
    }
    for name, (arity, predicate) in predicates.items():
        forbidden = [
            assignment
            for assignment in product((0, 1), repeat=arity)
            if predicate(assignment)
        ]
        assert audit_predicate(
            arity,
            forbidden,
            verify_restriction=True,
            report_witnesses=True,
        )
        print(
            f"Fanizza {name}: arity={arity}, forbidden={len(forbidden)}, "
            "all three common hyperplanes verified"
        )


if __name__ == "__main__":
    exhaustive()
    audit_fanizza_menu()
