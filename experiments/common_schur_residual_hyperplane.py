#!/usr/bin/env python3
"""Audit a common codimension-one Schur residual for values and resets.

For a cross-pairing U, fixed hyperplanes ker(alpha^T) and ker(beta^T)
restrict U nondegenerately iff beta^T U^-1 alpha = 1.  The invertible-
direction compiler realizes U as multiplication by a field element.  This
script solves the exact F2 system for the archived arity-one through arity-four
certificates and checks both all affine values and every nonzero reset
direction.
"""

from __future__ import annotations

import json
from itertools import product

from invertible_direction_schur_compiler import (
    KNOWN_MODULI,
    affine_values,
    gf_inv,
    gf_mul,
    multiplication_matrix,
    rank_matrix,
    search_certificate,
)


def dot(left: int, right: int) -> int:
    return (left & right).bit_count() & 1


def solve_constant_one(vectors: list[int], degree: int) -> int | None:
    """Return beta with <beta,v>=1 for every v, or None."""
    rows = [vector | (1 << degree) for vector in vectors]
    pivot_columns: list[int] = []
    rank = 0
    for column in range(degree):
        pivot = next(
            (index for index in range(rank, len(rows))
             if (rows[index] >> column) & 1),
            None,
        )
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for index in range(len(rows)):
            if index != rank and ((rows[index] >> column) & 1):
                rows[index] ^= rows[rank]
        pivot_columns.append(column)
        rank += 1
    mask = (1 << degree) - 1
    if any((row & mask) == 0 and ((row >> degree) & 1) for row in rows):
        return None
    beta = 0
    for row, column in zip(rows[:rank], pivot_columns):
        if (row >> degree) & 1:
            beta |= 1 << column
    assert all(dot(beta, vector) == 1 for vector in vectors)
    return beta


def hyperplane_basis(functional: int, degree: int) -> list[int]:
    vectors: list[int] = []
    pivot = (functional & -functional).bit_length() - 1
    for column in range(degree):
        if column == pivot:
            continue
        vector = 1 << column
        if (functional >> column) & 1:
            vector |= 1 << pivot
        vectors.append(vector)
    assert len(vectors) == degree - 1
    assert all(dot(functional, vector) == 0 for vector in vectors)
    return vectors


def restricted_matrix(
    multiplier: int,
    left_basis: list[int],
    right_basis: list[int],
    modulus: int,
    degree: int,
) -> list[list[int]]:
    return [
        [dot(left, gf_mul(multiplier, right, modulus, degree))
         for right in right_basis]
        for left in left_basis
    ]


def audit(k: int) -> dict:
    certificate = search_certificate(k)
    degree = certificate["matrix_size"]
    modulus = int(certificate["modulus_hex"], 16)
    a0 = int(certificate["a0_hex"], 16)
    directions = [int(value, 16) for value in certificate["directions_hex"]]
    values = affine_values(a0, directions)
    reset_values = []
    for bits in product((0, 1), repeat=k):
        value = 0
        for bit, direction in zip(bits, directions):
            if bit:
                value ^= direction
        if value:
            reset_values.append(value)

    alpha = 1
    value_reciprocals = [gf_inv(value, modulus, degree) for value in values]
    reset_reciprocals = [gf_inv(value, modulus, degree) for value in reset_values]
    beta_values = solve_constant_one(value_reciprocals, degree)
    beta_all = solve_constant_one(value_reciprocals + reset_reciprocals, degree)

    record = {
        "arity": k,
        "matrix_size": degree,
        "alpha_hex": hex(alpha),
        "beta_values_hex": None if beta_values is None else hex(beta_values),
        "beta_all_hex": None if beta_all is None else hex(beta_all),
        "value_forms": len(values),
        "nonzero_reset_forms": len(reset_values),
        "reset_values_hex": [hex(value) for value in reset_values],
        "value_only_common_residual": beta_values is not None,
        "value_and_all_resets_common_residual": beta_all is not None,
    }

    beta = beta_all if beta_all is not None else beta_values
    if beta is not None:
        left_basis = hyperplane_basis(alpha, degree)
        right_basis = hyperplane_basis(beta, degree)
        record["value_restriction_ranks"] = [
            rank_matrix(restricted_matrix(
                value, left_basis, right_basis, modulus, degree))
            for value in values
        ]
        record["reset_restriction_ranks"] = [
            rank_matrix(restricted_matrix(
                value, left_basis, right_basis, modulus, degree))
            for value in reset_values
        ]
        compatible_resets = [
            value
            for value, rank in zip(
                reset_values, record["reset_restriction_ranks"])
            if rank == degree - 1
        ]
        compatible_set = set(compatible_resets)
        record["compatible_reset_values_hex"] = [
            hex(value) for value in compatible_resets
        ]
        compatible_planes = {
            tuple(sorted((left, right, left ^ right)))
            for index, left in enumerate(compatible_resets)
            for right in compatible_resets[index + 1:]
            if (left ^ right) in compatible_set
        }
        record["compatible_reset_planes_hex"] = [
            [hex(value) for value in plane]
            for plane in sorted(compatible_planes)
        ]
    return record


def main() -> None:
    records = [audit(k) for k in range(1, 5)]
    print(json.dumps({
        "all_value_residuals": all(
            record["value_only_common_residual"] for record in records),
        "all_value_and_reset_residuals": all(
            record["value_and_all_resets_common_residual"] for record in records),
        "records": records,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
