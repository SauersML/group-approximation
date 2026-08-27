"""Exact Smith invariants of finite SL(3,Z) relator maps.

For the integer map d1:Z^edges -> Z^cells, nonunit Smith factors measure the
finite quotient between the image lattice and its saturation

    (ran_R(d1) cap Z^cells) / d1(Z^edges).

The computation is exact.  It is intended for small primes; FLINT receives a
dense integer matrix, so larger charts should use a sparse modular algorithm
instead of this script.
"""

import argparse
import json
import time

from flint import fmpz_mat

from sl3_degree_one_spectrum import coboundaries


def run(prime):
    started = time.time()
    _names, vertices, _d0, d1 = coboundaries(prime)
    matrix = fmpz_mat(d1.toarray().astype(int).tolist())
    smith = matrix.snf()
    diagonal_length = min(smith.nrows(), smith.ncols())
    factors = [abs(int(smith[index, index]))
               for index in range(diagonal_length)
               if smith[index, index] != 0]
    expected_rank = d1.shape[1] - (vertices - 1)
    if len(factors) != expected_rank:
        raise AssertionError("Smith rank differs from expected real rank")
    nonunit = [factor for factor in factors if factor != 1]
    torsion_order = 1
    for factor in nonunit:
        torsion_order *= factor
    return {
        "prime": prime,
        "vertices": vertices,
        "edges": int(d1.shape[1]),
        "cells": int(d1.shape[0]),
        "rank": len(factors),
        "unit_factors": len(factors) - len(nonunit),
        "nonunit_factors": nonunit,
        "saturation_quotient_order": torsion_order,
        "image_is_saturated": not nonunit,
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", type=int, nargs="+", required=True)
    args = parser.parse_args()
    for prime in args.primes:
        print(json.dumps(run(prime)), flush=True)


if __name__ == "__main__":
    main()
