"""Reduce a chart-dependent integral projection by nearest-plane decoding.

Every integral left inverse ``R`` of a primitive range basis ``L`` differs
from a fixed one by rows in the primitive cycle lattice.  This script LLL
reduces that cycle lattice once and applies Babai nearest-plane reduction to
every row of ``R``.  It then certifies the resulting integral projection

    P=L R,  P^2=P,  P A=A

exactly and reports the norm of ``I-P`` before and after reduction.

This is a fast synthesis baseline, not an optimal CVP certificate.
"""

import argparse
import json
import time

import numpy as np
from fpylll import BKZ, GSO, IntegerMatrix, LLL
from sage.all import matrix

from sl3_carry_rational_projection import (
    exact_norm_summary,
    identity,
    integer_matrix,
    integral_right_inverse,
    primitive_range_basis,
)
from sl3_projective_charts import projective_coboundaries


def spectral_norm(value):
    return float(np.linalg.norm(np.asarray(value, dtype=np.float64), ord=2))


def projection_summary(projection):
    complement = identity(projection.nrows()) - projection
    return {
        "projection": exact_norm_summary(projection),
        "complement": {
            **exact_norm_summary(complement),
            "spectral_norm_numerical": spectral_norm(complement),
        },
    }


def reduced_cycle_basis(cycles, block_size):
    basis = IntegerMatrix.from_matrix([
        [int(cycles[row, column]) for column in range(cycles.ncols())]
        for row in range(cycles.nrows())
    ])
    LLL.reduction(basis, delta=0.99)
    if block_size:
        BKZ.reduction(basis, BKZ.Param(block_size=block_size))
    return basis


def nearest_plane_rows(right_inverse, cycles, block_size):
    basis = reduced_cycle_basis(cycles, block_size)
    orthogonalization = GSO.Mat(basis, float_type="double")
    orthogonalization.update_gso()
    reduced = matrix(right_inverse)
    before_squared = []
    after_squared = []
    for column in range(right_inverse.ncols()):
        original = [int(right_inverse[row, column])
                    for row in range(right_inverse.nrows())]
        coefficients = orthogonalization.babai(tuple(-value
                                                     for value in original))
        correction = [
            sum(int(coefficients[row]) * int(basis[row, coordinate])
                for row in range(basis.nrows))
            for coordinate in range(basis.ncols)
        ]
        updated = [value + delta
                   for value, delta in zip(original, correction)]
        for row, value in enumerate(updated):
            reduced[row, column] = value
        before_squared.append(sum(value * value for value in original))
        after_squared.append(sum(value * value for value in updated))
    return reduced, before_squared, after_squared


def run(prime, block_size):
    started = time.time()
    _names, vertices, _d0, sparse = projective_coboundaries(prime)
    relator = integer_matrix(sparse)
    cycles, range_basis = primitive_range_basis(relator)
    range_rows = range_basis.transpose()
    initial_right_inverse = integral_right_inverse(range_rows)
    reduced_right_inverse, before_squared, after_squared = nearest_plane_rows(
        initial_right_inverse, cycles, block_size)

    rank = range_rows.nrows()
    if range_rows * reduced_right_inverse != identity(rank):
        raise AssertionError("cycle reduction changed the right-inverse equation")
    initial_projection = range_basis * initial_right_inverse.transpose()
    reduced_projection = range_basis * reduced_right_inverse.transpose()
    if reduced_projection * reduced_projection != reduced_projection:
        raise AssertionError("reduced projection is not idempotent")
    if reduced_projection * relator != relator:
        raise AssertionError("reduced projection does not fix the relator range")

    return {
        "chart": "projective",
        "prime": prime,
        "vertices": vertices,
        "edges": relator.ncols(),
        "cells": relator.nrows(),
        "rank": rank,
        "cycle_rank": cycles.nrows(),
        "reduction": "LLL+Babai" if not block_size else "BKZ+Babai",
        "bkz_block_size": block_size,
        "right_inverse_row_norm_squared": {
            "before_sum": str(sum(before_squared)),
            "after_sum": str(sum(after_squared)),
            "before_max": str(max(before_squared)),
            "after_max": str(max(after_squared)),
        },
        "before": projection_summary(initial_projection),
        "after": projection_summary(reduced_projection),
        "identities": {
            "R_L_equals_identity": True,
            "P_squared_equals_P": True,
            "P_A_equals_A": True,
        },
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, required=True)
    parser.add_argument("--bkz-block-size", type=int, default=0)
    args = parser.parse_args()
    if args.bkz_block_size and args.bkz_block_size < 2:
        parser.error("--bkz-block-size must be zero or at least two")
    print(json.dumps(run(args.prime, args.bkz_block_size)), flush=True)


if __name__ == "__main__":
    main()
