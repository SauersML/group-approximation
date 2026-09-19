#!/usr/bin/env python3
"""Audit GL2 symmetry of compatible rank-fifteen reset pencils over F2.

For an ordered invertible pair (B1,B2), strict equivalence of the pencil
under the two generators swapping B1,B2 and fixing B1 while replacing B2 by
B1+B2 is equivalent to similarity of T=B1^-1 B2 with T^-1 and I+T.
Similarity is decided exactly from the nullities of powers of every primary
polynomial factor.
"""

from __future__ import annotations

import json

import sympy

from common_schur_residual_hyperplane import (
    hyperplane_basis,
    restricted_matrix,
)
from invertible_direction_schur_compiler import (
    gf_inv,
    rank_matrix,
    search_certificate,
)


def identity(size: int) -> list[list[int]]:
    return [[int(row == column) for column in range(size)] for row in range(size)]


def add(left: list[list[int]], right: list[list[int]]) -> list[list[int]]:
    return [
        [a ^ b for a, b in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def multiply(left: list[list[int]], right: list[list[int]]) -> list[list[int]]:
    size = len(left)
    return [
        [
            sum(left[row][middle] * right[middle][column] for middle in range(size)) & 1
            for column in range(size)
        ]
        for row in range(size)
    ]


def inverse(matrix: list[list[int]]) -> list[list[int]]:
    size = len(matrix)
    rows = [
        sum(bit << column for column, bit in enumerate(row)) | (1 << (size + index))
        for index, row in enumerate(matrix)
    ]
    for column in range(size):
        pivot = next(index for index in range(column, size) if (rows[index] >> column) & 1)
        rows[column], rows[pivot] = rows[pivot], rows[column]
        for index in range(size):
            if index != column and ((rows[index] >> column) & 1):
                rows[index] ^= rows[column]
    mask = (1 << size) - 1
    assert all((rows[index] & mask) == (1 << index) for index in range(size))
    return [
        [((rows[row] >> (size + column)) & 1) for column in range(size)]
        for row in range(size)
    ]


def polynomial_at(coefficients: list[int], matrix: list[list[int]]) -> list[list[int]]:
    """Evaluate coefficients in descending order by Horner's rule."""
    size = len(matrix)
    result = [[0 for _ in range(size)] for _ in range(size)]
    unit = identity(size)
    for coefficient in coefficients:
        result = multiply(result, matrix)
        if coefficient & 1:
            result = add(result, unit)
    return result


def similarity_signature(matrix: list[list[int]]) -> dict:
    size = len(matrix)
    symbol = sympy.Symbol("x")
    characteristic = sympy.Poly(
        sympy.Matrix(matrix).charpoly(symbol).as_expr(), symbol, modulus=2
    )
    _, factors = sympy.factor_list(characteristic, modulus=2)
    primary = []
    for factor, multiplicity in factors:
        coefficients = [int(value) & 1 for value in factor.all_coeffs()]
        evaluated = polynomial_at(coefficients, matrix)
        power = identity(size)
        nullities = []
        for _ in range(1, multiplicity + 1):
            power = multiply(power, evaluated)
            nullities.append(size - rank_matrix(power))
        primary.append({
            "factor": str(factor.as_expr()),
            "multiplicity": multiplicity,
            "nullities": nullities,
        })
    return {
        "characteristic_polynomial": str(characteristic.as_expr()),
        "primary_data": primary,
    }


def main() -> None:
    certificate = search_certificate(4)
    degree = certificate["matrix_size"]
    modulus = int(certificate["modulus_hex"], 16)
    alpha = 0x1
    beta = 0x4DDC
    left_basis = hyperplane_basis(alpha, degree)
    right_basis = hyperplane_basis(beta, degree)

    compatible = [
        0x2CE6, 0xB0EB, 0x9C0D, 0x762, 0x2B84,
        0xB789, 0xB8AA, 0x24A7, 0x841,
    ]
    compatible_set = set(compatible)
    planes = sorted({
        tuple(sorted((left, right, left ^ right)))
        for index, left in enumerate(compatible)
        for right in compatible[index + 1:]
        if (left ^ right) in compatible_set
    })

    records = []
    for plane in planes:
        first, second, third = plane
        forms = [
            restricted_matrix(value, left_basis, right_basis, modulus, degree)
            for value in plane
        ]
        assert all(rank_matrix(form) == degree - 1 for form in forms)
        transition = multiply(inverse(forms[0]), forms[1])
        inverse_transition = inverse(transition)
        translated_transition = add(identity(degree - 1), transition)
        signature = similarity_signature(transition)
        inverse_signature = similarity_signature(inverse_transition)
        translated_signature = similarity_signature(translated_transition)
        records.append({
            "plane_hex": [hex(value) for value in plane],
            "third_is_xor": first ^ second == third,
            "transition_invertible": rank_matrix(transition) == degree - 1,
            "translated_transition_invertible": rank_matrix(translated_transition) == degree - 1,
            "swap_similarity": signature == inverse_signature,
            "shear_similarity": signature == translated_signature,
            "signature": signature,
        })

    print(json.dumps({
        "matrix_size": degree,
        "residual_size": degree - 1,
        "plane_count": len(records),
        "s3_symmetric_plane_count": sum(
            record["swap_similarity"] and record["shear_similarity"]
            for record in records
        ),
        "records": records,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
