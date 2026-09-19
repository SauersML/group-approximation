"""Exact transfer-surjectivity certificates for finite SL(3,Z) charts.

Let S sum relator-cell coordinates over the finite chart.  Instead of
constructing the large lattice ker(d1^T), form the combined integer map

    k |-> (d1^T k, S k).

Its row matrix has rational rank rank(d1)+rank(K_1), where K_1 is the
trivial-chart cycle lattice.  A gcd-one collection of maximal minors proves
that its integer image is saturated.  Every (0,v), v in K_1, has the
rational preimage |X|^{-1} Jv, so saturation proves S(K_X)=K_1 exactly.
"""

import argparse
import json
import math
import time

import numpy as np
from flint import fmpz_mat

from sl3_carry_minor_certificate import (
    candidate_record,
    select_minor_modular,
)
from sl3_degree_one_spectrum import (
    ROOTS,
    coboundaries,
    presentation_relators,
)


def base_cycle_rank():
    _names, relators = presentation_relators()
    exponent_matrix = fmpz_mat([
        [sum(sign for generator, sign in word if generator == column)
         for column in range(len(ROOTS))]
        for word in relators
    ])
    return exponent_matrix.nrows() - int(exponent_matrix.rank())


def combined_row_matrix(chart_prime):
    names, vertices, _d0, d1 = coboundaries(chart_prime)
    dense = d1.toarray().astype(np.int64)
    combined = np.zeros(
        (d1.shape[0], d1.shape[1] + len(names)), dtype=np.int64)
    combined[:, :d1.shape[1]] = dense
    for row in range(d1.shape[0]):
        combined[row, d1.shape[1] + row // vertices] = 1
    expected_rank = d1.shape[1] - (vertices - 1) + base_cycle_rank()
    return names, vertices, d1, combined, expected_rank


def run(chart_prime, selection_primes):
    started = time.time()
    names, vertices, d1, combined, expected_rank = combined_row_matrix(
        chart_prime)
    candidates = []
    determinant_gcd = 0
    for coefficient_prime in selection_primes:
        rows, columns, determinant = select_minor_modular(
            combined, expected_rank, coefficient_prime)
        determinant_gcd = math.gcd(determinant_gcd, abs(determinant))
        candidates.append(candidate_record(
            "mod_%d" % coefficient_prime, rows, columns, determinant))
        if determinant_gcd == 1:
            break
    return {
        "chart_prime": chart_prime,
        "vertices": vertices,
        "edges": int(d1.shape[1]),
        "cells": int(d1.shape[0]),
        "base_cycle_rank": base_cycle_rank(),
        "combined_rational_rank": expected_rank,
        "determinant_gcd": str(determinant_gcd),
        "combined_image_saturated": determinant_gcd == 1,
        "cycle_transfer_surjective": determinant_gcd == 1,
        "minors": candidates,
        "elapsed_s": round(time.time() - started, 3),
    }


def verify(path):
    with open(path, "r", encoding="utf-8") as stream:
        certificate = json.load(stream)
    chart_prime = int(certificate["chart_prime"])
    _names, _vertices, _d1, combined, expected_rank = combined_row_matrix(
        chart_prime)
    if expected_rank != int(certificate["combined_rational_rank"]):
        raise AssertionError("combined rank does not match certificate")
    determinant_gcd = 0
    verified = []
    for candidate in certificate["minors"]:
        rows = np.asarray(candidate["row_indices"], dtype=np.int64)
        columns = np.asarray(candidate["column_indices"], dtype=np.int64)
        if len(rows) != expected_rank or len(columns) != expected_rank:
            raise AssertionError("minor has the wrong dimension")
        determinant = int(fmpz_mat(
            combined[np.ix_(rows, columns)].tolist()).det())
        if str(determinant) != candidate["determinant"]:
            raise AssertionError("stored determinant does not verify")
        determinant_gcd = math.gcd(determinant_gcd, abs(determinant))
        verified.append({
            "selection": candidate["selection"],
            "determinant": str(determinant),
        })
    if str(determinant_gcd) != certificate["determinant_gcd"]:
        raise AssertionError("stored determinant gcd does not verify")
    return {
        "chart_prime": chart_prime,
        "combined_rational_rank": expected_rank,
        "verified_minors": verified,
        "determinant_gcd": str(determinant_gcd),
        "combined_image_saturated": determinant_gcd == 1,
        "cycle_transfer_surjective": determinant_gcd == 1,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--chart-prime", type=int)
    parser.add_argument("--selection-primes", type=int, nargs="+",
                        default=(2, 3, 5, 7, 11))
    parser.add_argument("--verify")
    args = parser.parse_args()
    if args.verify:
        print(json.dumps(verify(args.verify)))
        return
    if args.chart_prime is None:
        parser.error("--chart-prime is required unless --verify is used")
    print(json.dumps(run(args.chart_prime, args.selection_primes)))


if __name__ == "__main__":
    main()
