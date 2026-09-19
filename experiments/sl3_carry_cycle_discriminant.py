"""Exact primitive cycle-discriminant arithmetic for finite SL(3,Z) charts.

For A=d1, the cycle lattice controlling integral carry transversality is

    K = ker(A^T) intersect Z^cells.

The zero rows in a transformed row Hermite form of A give a primitive
integer basis C of K.  This script certifies primitivity, computes the Smith
invariants of C^T C, and evaluates the fixed-axis torsion-cell witness with
exact rational arithmetic.  It is intended for the small calibration chart;
the full discriminant group is already too large to enumerate there.
"""

import argparse
import json
import math
import time

from flint import fmpq_mat, fmpz, fmpz_mat

from sl3_degree_one_spectrum import coboundaries, nonzero_vectors


def primitive_cycle_basis(d1):
    matrix = fmpz_mat(d1.toarray().astype(int).tolist())
    hermite, transform = matrix.hnf(transform=True)
    zero_rows = [
        row for row in range(hermite.nrows())
        if all(hermite[row, column] == 0
               for column in range(hermite.ncols()))
    ]
    basis = fmpz_mat([
        [transform[row, column] for row in zero_rows]
        for column in range(transform.ncols())
    ])
    transpose = fmpz_mat(d1.T.toarray().astype(int).tolist())
    if not (transpose * basis).is_zero():
        raise AssertionError("Hermite zero rows do not lie in the kernel")
    smith = basis.snf()
    factors = [
        abs(int(smith[index, index]))
        for index in range(min(smith.nrows(), smith.ncols()))
        if smith[index, index] != 0
    ]
    if len(factors) != len(zero_rows) or any(value != 1 for value in factors):
        raise AssertionError("cycle basis is not primitive")
    return basis


def factorization(value):
    return [[int(prime), int(exponent)]
            for prime, exponent in fmpz(value).factor()]


def run(prime):
    started = time.time()
    names, vertices, _d0, d1 = coboundaries(prime)
    basis = primitive_cycle_basis(d1)
    gram = basis.transpose() * basis
    gram_smith = gram.snf()
    gram_factors = [abs(int(gram_smith[index, index]))
                    for index in range(gram_smith.nrows())]
    determinant = int(gram.det())

    points = nonzero_vectors(prime)
    fixed = [index for index, point in enumerate(points)
             if tuple(map(int, point)) == (0, 0, 1)]
    if len(fixed) != 1:
        raise AssertionError("fixed-axis point is not unique")
    row = names.index("crw_torsion") * vertices + fixed[0]
    coordinates = fmpz_mat([[basis[row, column]]
                            for column in range(basis.ncols())])
    solution = fmpq_mat(gram).solve(fmpq_mat(coordinates))
    distance_squared = sum(
        fmpq_mat(coordinates)[index, 0] * solution[index, 0]
        for index in range(coordinates.nrows())
    )
    class_order = 1
    for index in range(solution.nrows()):
        class_order = math.lcm(
            class_order, int(solution[index, 0].denominator))

    nonunit = [value for value in gram_factors if value != 1]
    return {
        "prime": prime,
        "vertices": vertices,
        "cells": int(d1.shape[0]),
        "cycle_rank": basis.ncols(),
        "cycle_basis_primitive": True,
        "gram_determinant": str(determinant),
        "gram_determinant_bits": abs(determinant).bit_length(),
        "gram_determinant_factorization": factorization(abs(determinant)),
        "gram_smith_unit_factors": len(gram_factors) - len(nonunit),
        "gram_smith_nonunit_factors": [str(value) for value in nonunit],
        "fixed_axis_torsion_cell": {
            "row": row,
            "distance_squared": str(distance_squared),
            "theta_squared_lower": str(1 / distance_squared),
            "discriminant_class_order": str(class_order),
            "discriminant_class_order_factorization": factorization(
                class_order),
        },
        "elapsed_s": round(time.time() - started, 3),
    }


def verify(path):
    with open(path, "r", encoding="utf-8") as stream:
        expected = json.load(stream)
    actual = run(int(expected["prime"]))
    expected.pop("elapsed_s", None)
    actual.pop("elapsed_s", None)
    if actual != expected:
        raise AssertionError("stored discriminant result does not verify")
    return {"valid": True, **actual}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int)
    parser.add_argument("--verify")
    args = parser.parse_args()
    if args.verify:
        print(json.dumps(verify(args.verify)))
        return
    if args.prime is None:
        parser.error("--prime is required unless --verify is used")
    print(json.dumps(run(args.prime)))


if __name__ == "__main__":
    main()
