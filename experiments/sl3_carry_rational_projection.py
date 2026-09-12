"""Exact rational splitting of a finite SL(3,Z) relator range.

Run this file with SageMath.  For ``A=d1`` write ``A=L X``, where the
columns of ``L`` are a basis of the saturated range lattice.  Smith
transformations construct an integral projection ``P`` onto that lattice
and a denominator-cleared generalized inverse ``C`` satisfying

    P^2=P,  P A=A,  A C=M P,  A C A=M A.

The finite denominator ``M`` is the exponent of the saturation quotient.
Exact coefficient norms measure how poorly conditioned this particular
integral splitting is.  The construction is chart-dependent and does not
compute the optimal projection or the carry constant Theta.
"""

import argparse
import hashlib
import json
import math
import time

import numpy as np
from sage.all import ZZ, matrix

from sl3_degree_one_spectrum import coboundaries
from sl3_projective_charts import projective_coboundaries


def identity(size):
    return matrix.identity(ZZ, size, sparse=True)


def integer_matrix(sparse_matrix):
    return matrix(
        ZZ, sparse_matrix.toarray().astype(int).tolist(), sparse=True)


def primitive_range_basis(relator):
    """Return L with columns spanning ran_R(A) intersect Z^cells."""
    cycles = relator.left_kernel_matrix()
    range_rows = cycles.right_kernel_matrix()
    if cycles * range_rows.transpose() != 0:
        raise AssertionError("primitive range basis is not orthogonal to cycles")
    return cycles, range_rows.transpose()


def integral_right_inverse(primitive_rows):
    """Return V with primitive_rows*V=I using Smith transformations."""
    diagonal, left, right = primitive_rows.smith_form(transformation=True)
    rank = primitive_rows.nrows()
    expected = matrix(ZZ, rank, primitive_rows.ncols(), sparse=True)
    for index in range(rank):
        expected[index, index] = 1
    if diagonal != expected:
        raise AssertionError("row lattice is not primitive")
    inclusion = matrix(ZZ, primitive_rows.ncols(), rank, sparse=True)
    for index in range(rank):
        inclusion[index, index] = 1
    result = right * inclusion * left
    if primitive_rows * result != identity(rank):
        raise AssertionError("integral right inverse does not verify")
    return result


def denominator_inverse(coordinate_map):
    """Return M,Y with coordinate_map*Y=M I exactly."""
    diagonal, left, right = coordinate_map.smith_form(transformation=True)
    rank = coordinate_map.nrows()
    factors = [abs(ZZ(diagonal[index, index])) for index in range(rank)]
    if any(factor == 0 for factor in factors):
        raise AssertionError("coordinate map does not have full row rank")
    denominator = math.lcm(*(int(factor) for factor in factors))
    lifted = matrix(ZZ, coordinate_map.ncols(), rank, sparse=True)
    for index, factor in enumerate(factors):
        for column in range(rank):
            lifted[index, column] = (
                ZZ(denominator // int(factor)) * left[index, column])
    result = right * lifted
    if coordinate_map * result != denominator * identity(rank):
        raise AssertionError("denominator-cleared inverse does not verify")
    return denominator, [int(factor) for factor in factors], result


def matrix_hash(value):
    digest = hashlib.sha256()
    for row in range(value.nrows()):
        digest.update(b"[")
        for column in range(value.ncols()):
            digest.update(str(int(value[row, column])).encode("ascii"))
            digest.update(b",")
        digest.update(b"]")
    return digest.hexdigest()


def exact_norm_summary(value):
    row_sums = [sum(abs(int(entry)) for entry in value.row(row))
                for row in range(value.nrows())]
    column_sums = [sum(abs(int(entry)) for entry in value.column(column))
                   for column in range(value.ncols())]
    frobenius_squared = sum(int(entry) ** 2 for entry in value.list())
    maximum = max(abs(int(entry)) for entry in value.list())
    one_norm = max(column_sums)
    infinity_norm = max(row_sums)
    return {
        "coefficient_max": maximum,
        "one_norm": one_norm,
        "infinity_norm": infinity_norm,
        "spectral_upper_squared": one_norm * infinity_norm,
        "frobenius_squared": str(frobenius_squared),
        "sha256": matrix_hash(value),
    }


def run(prime, chart):
    started = time.time()
    builder = (projective_coboundaries if chart == "projective"
               else coboundaries)
    _names, vertices, _d0, sparse = builder(prime)
    relator = integer_matrix(sparse)
    cycles, range_basis = primitive_range_basis(relator)

    right_inverse = integral_right_inverse(range_basis.transpose())
    left_inverse = right_inverse.transpose()
    coordinate_map = left_inverse * relator
    if range_basis * coordinate_map != relator:
        raise AssertionError("saturated range factorization does not verify")

    denominator, factors, cleared_inverse = denominator_inverse(
        coordinate_map)
    projection = range_basis * left_inverse
    certificate = cleared_inverse * left_inverse
    complement = identity(relator.nrows()) - projection

    if projection * projection != projection:
        raise AssertionError("projection is not idempotent")
    if projection * relator != relator:
        raise AssertionError("projection does not fix the relator range")
    if relator * certificate != denominator * projection:
        raise AssertionError("A C is not M P")
    if relator * certificate * relator != denominator * relator:
        raise AssertionError("A C A is not M A")

    complement_float = np.asarray(complement, dtype=np.float64)
    spectral_norm = float(np.linalg.norm(complement_float, ord=2))
    nonunit = [factor for factor in factors if factor != 1]
    return {
        "chart": chart,
        "prime": prime,
        "vertices": vertices,
        "edges": relator.ncols(),
        "cells": relator.nrows(),
        "rank": range_basis.ncols(),
        "cycle_rank": cycles.nrows(),
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
        "denominator_cleared_inverse": exact_norm_summary(cleared_inverse),
        "certificate_C": exact_norm_summary(certificate),
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, required=True)
    parser.add_argument("--chart", choices=("projective", "vectors"),
                        required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.prime, args.chart)), flush=True)


if __name__ == "__main__":
    main()
