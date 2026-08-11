"""Exact rational splitting of the saturated relator range on one chart.

For the integer relator map ``A=d1`` write

    A = L X,

where the columns of ``L`` form a basis of the saturated range lattice.
An integral left inverse ``R`` of ``L`` gives the chart-dependent integral
projection ``P=L R`` onto the real range.  If ``M`` is the exponent of
``Z^rank(X) / X Z^edges``, exact Hermite arithmetic constructs ``Y`` with

    X Y = M I.

Consequently ``C=Y R`` is an integer matrix satisfying

    A C A = M A,       A C = M P.

Thus ``B=C/M`` is a rational generalized inverse while ``A B=P`` preserves
the cell lattice.  The script reports exact coefficient norms and hashes,
plus the numerical spectral norm of ``I-P``.  The latter is diagnostic only;
all algebraic identities are checked over the integers.

This is intended for small calibration charts.  It does not bound the
optimal integral projection norm and it does not compute the carry constant
Theta.
"""

import argparse
import hashlib
import json
import math
import time

import numpy as np
from flint import fmpq_mat, fmpz_mat

from sl3_degree_one_spectrum import coboundaries


def integer_matrix(sparse_matrix):
    return fmpz_mat(sparse_matrix.toarray().astype(int).tolist())


def identity(size):
    result = fmpz_mat(size, size)
    for index in range(size):
        result[index, index] = 1
    return result


def selected_rows(matrix, rows):
    return fmpz_mat([
        [matrix[row, column] for column in range(matrix.ncols())]
        for row in rows
    ])


def nonzero_rows(matrix):
    return [
        row for row in range(matrix.nrows())
        if any(matrix[row, column] != 0
               for column in range(matrix.ncols()))
    ]


def left_kernel_basis(matrix):
    """Return a primitive column basis of ker(matrix^T) over Z."""
    hermite, transform = matrix.hnf(transform=True)
    zero_rows = [row for row in range(hermite.nrows())
                 if row not in set(nonzero_rows(hermite))]
    basis = fmpz_mat([
        [transform[row, column] for row in zero_rows]
        for column in range(transform.ncols())
    ])
    if not (matrix.transpose() * basis).is_zero():
        raise AssertionError("Hermite kernel basis does not verify")
    return basis


def integral_left_inverse(primitive_basis):
    """Construct R with R L=I for a primitive full-column-rank matrix L."""
    hermite, transform = primitive_basis.hnf(transform=True)
    rows = nonzero_rows(hermite)
    reduced = selected_rows(hermite, rows)
    expected = identity(primitive_basis.ncols())
    if reduced != expected:
        raise AssertionError("basis is not primitive in the ambient lattice")
    left_inverse = selected_rows(transform, rows)
    if left_inverse * primitive_basis != expected:
        raise AssertionError("integral left inverse does not verify")
    return left_inverse


def integral_solution(matrix, right_hand_side):
    """Solve a square full-rank integer system known to have integral output."""
    rational = fmpq_mat(matrix).solve(fmpq_mat(right_hand_side))
    result = fmpz_mat(rational.nrows(), rational.ncols())
    for row in range(rational.nrows()):
        for column in range(rational.ncols()):
            value = rational[row, column]
            if value.denominator != 1:
                raise AssertionError("chosen denominator does not clear the image")
            result[row, column] = value.numerator
    return result


def matrix_hash(matrix):
    digest = hashlib.sha256()
    for row in range(matrix.nrows()):
        digest.update(b"[")
        for column in range(matrix.ncols()):
            digest.update(str(int(matrix[row, column])).encode("ascii"))
            digest.update(b",")
        digest.update(b"]")
    return digest.hexdigest()


def exact_norm_summary(matrix):
    row_sums = [sum(abs(int(matrix[row, column]))
                    for column in range(matrix.ncols()))
                for row in range(matrix.nrows())]
    column_sums = [sum(abs(int(matrix[row, column]))
                       for row in range(matrix.nrows()))
                   for column in range(matrix.ncols())]
    frobenius_squared = sum(
        int(matrix[row, column]) ** 2
        for row in range(matrix.nrows())
        for column in range(matrix.ncols())
    )
    maximum = max(
        abs(int(matrix[row, column]))
        for row in range(matrix.nrows())
        for column in range(matrix.ncols())
    )
    one_norm = max(column_sums)
    infinity_norm = max(row_sums)
    return {
        "coefficient_max": maximum,
        "one_norm": one_norm,
        "infinity_norm": infinity_norm,
        "spectral_upper_squared": one_norm * infinity_norm,
        "frobenius_squared": str(frobenius_squared),
        "sha256": matrix_hash(matrix),
    }


def run(prime):
    started = time.time()
    _names, vertices, _d0, sparse = coboundaries(prime)
    relator = integer_matrix(sparse)
    cycle_basis = left_kernel_basis(relator)
    range_basis = left_kernel_basis(cycle_basis)
    left_inverse = integral_left_inverse(range_basis)

    coordinate_map = left_inverse * relator
    if range_basis * coordinate_map != relator:
        raise AssertionError("saturated range factorization does not verify")

    smith = coordinate_map.snf()
    factors = [
        abs(int(smith[index, index]))
        for index in range(min(smith.nrows(), smith.ncols()))
        if smith[index, index] != 0
    ]
    if len(factors) != range_basis.ncols():
        raise AssertionError("coordinate map does not have full row rank")
    denominator = math.lcm(*factors)

    image_hermite, image_transform = coordinate_map.transpose().hnf(
        transform=True)
    rows = nonzero_rows(image_hermite)
    image_basis = selected_rows(image_hermite, rows)
    transform_rows = selected_rows(image_transform, rows)
    if image_basis.nrows() != range_basis.ncols():
        raise AssertionError("image Hermite basis has the wrong rank")

    scaled_identity = denominator * identity(range_basis.ncols())
    quotient = integral_solution(image_basis.transpose(), scaled_identity)
    denominator_inverse = transform_rows.transpose() * quotient
    if coordinate_map * denominator_inverse != scaled_identity:
        raise AssertionError("denominator-cleared right inverse does not verify")

    projection = range_basis * left_inverse
    certificate = denominator_inverse * left_inverse
    complement = identity(relator.nrows()) - projection
    if projection * projection != projection:
        raise AssertionError("projection is not idempotent")
    if projection * relator != relator:
        raise AssertionError("projection does not fix the relator range")
    if relator * certificate != denominator * projection:
        raise AssertionError("A C is not M P")
    if relator * certificate * relator != denominator * relator:
        raise AssertionError("A C A is not M A")

    complement_float = np.asarray(
        [[float(complement[row, column])
          for column in range(complement.ncols())]
         for row in range(complement.nrows())], dtype=np.float64)
    spectral_norm = float(np.linalg.norm(complement_float, ord=2))
    nonunit = [factor for factor in factors if factor != 1]
    return {
        "prime": prime,
        "vertices": vertices,
        "edges": relator.ncols(),
        "cells": relator.nrows(),
        "rank": range_basis.ncols(),
        "cycle_rank": cycle_basis.ncols(),
        "saturation_smith_nonunit_factors": nonunit,
        "saturation_exponent": denominator,
        "identities": {
            "A_equals_LX": True,
            "R_L_equals_identity": True,
            "P_squared_equals_P": True,
            "P_A_equals_A": True,
            "X_Y_equals_M_identity": True,
            "A_C_equals_M_P": True,
            "A_C_A_equals_M_A": True,
        },
        "left_inverse": exact_norm_summary(left_inverse),
        "projection": exact_norm_summary(projection),
        "projection_complement": {
            **exact_norm_summary(complement),
            "spectral_norm_numerical": spectral_norm,
        },
        "denominator_cleared_inverse": exact_norm_summary(
            denominator_inverse),
        "certificate_C": exact_norm_summary(certificate),
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.prime)), flush=True)


if __name__ == "__main__":
    main()
