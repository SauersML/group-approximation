"""Search for a unimodular maximal minor of the SL(3,Z) relator map.

A rank-r integer matrix has saturated image exactly when the gcd of its
r-by-r minors is one.  In particular, one minor of determinant +/-1 is an
immediate exact certificate.  Pivoted floating QR selects independent,
well-conditioned columns and rows; FLINT computes the selected determinant
with exact integer arithmetic.
"""

import argparse
import json
import math
import time

import numpy as np
from flint import fmpz, fmpz_mat, nmod_mat
from scipy.linalg import qr

from sl3_degree_one_spectrum import coboundaries


def select_minor(dense, dense_integer, rank, trial):
    if trial == 0:
        weighted = dense
    else:
        rng = np.random.default_rng(trial)
        row_weights = np.exp(rng.uniform(-1.0, 1.0, dense.shape[0]))
        column_weights = np.exp(rng.uniform(-1.0, 1.0, dense.shape[1]))
        weighted = row_weights[:, None] * dense * column_weights[None, :]
    _q_columns, r_columns, column_pivots = qr(
        weighted, mode="economic", pivoting=True, check_finite=False)
    columns = np.asarray(column_pivots[:rank], dtype=np.int64)
    selected_columns = weighted[:, columns]
    _q_rows, r_rows, row_pivots = qr(
        selected_columns.T, mode="economic", pivoting=True,
        check_finite=False)
    rows = np.asarray(row_pivots[:rank], dtype=np.int64)
    if (np.min(np.abs(np.diag(r_columns)[:rank])) < 1e-8 or
            np.min(np.abs(np.diag(r_rows)[:rank])) < 1e-8):
        raise AssertionError("QR did not select a full-rank minor")
    minor = dense_integer[np.ix_(rows, columns)]
    determinant = int(fmpz_mat(minor.tolist()).det())
    return rows, columns, determinant


def pivot_columns(reduced, rank):
    pivots = []
    for row in range(rank):
        for column in range(reduced.ncols()):
            if reduced[row, column] != 0:
                pivots.append(column)
                break
        else:
            raise AssertionError("nonzero reduced row has no pivot")
    return np.asarray(pivots, dtype=np.int64)


def select_minor_modular(dense_integer, rank, prime):
    reduced, modular_rank = nmod_mat(dense_integer.tolist(), prime).rref()
    if modular_rank != rank:
        raise ValueError("matrix rank drops modulo %d" % prime)
    columns = pivot_columns(reduced, rank)
    transpose = dense_integer[:, columns].T
    reduced_transpose, transpose_rank = nmod_mat(
        transpose.tolist(), prime).rref()
    if transpose_rank != rank:
        raise AssertionError("selected columns lose modular row rank")
    rows = pivot_columns(reduced_transpose, rank)
    minor = dense_integer[np.ix_(rows, columns)]
    determinant = int(fmpz_mat(minor.tolist()).det())
    if determinant % prime == 0:
        raise AssertionError("modularly selected minor is singular")
    return rows, columns, determinant


def candidate_record(label, rows, columns, determinant):
    absolute = abs(determinant)
    factors = (fmpz(absolute).factor()
               if absolute and absolute.bit_length() <= 128 else [])
    small_prime_divisors = [
        prime_factor for prime_factor in
        (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
        if absolute and absolute % prime_factor == 0
    ]
    return {
        "selection": label,
        "determinant": str(determinant),
        "determinant_bits": absolute.bit_length(),
        "factorization": [[int(factor), int(exponent)]
                          for factor, exponent in factors],
        "factorization_complete": bool(absolute.bit_length() <= 128),
        "small_prime_divisors": small_prime_divisors,
        "row_indices": [int(row) for row in rows],
        "column_indices": [int(column) for column in columns],
    }


def run(prime, trials, modular_primes):
    started = time.time()
    _names, vertices, _d0, d1 = coboundaries(prime)
    rank = d1.shape[1] - (vertices - 1)
    dense_integer = d1.toarray().astype(np.int64)
    dense = dense_integer.astype(np.float64)
    candidates = []
    determinant_gcd = 0
    for trial in range(trials):
        rows, columns, determinant = select_minor(
            dense, dense_integer, rank, trial)
        absolute = abs(determinant)
        determinant_gcd = math.gcd(determinant_gcd, absolute)
        candidates.append(candidate_record(
            "qr_%d" % trial, rows, columns, determinant))
        if determinant_gcd == 1:
            break
    for coefficient_prime in modular_primes:
        if determinant_gcd == 1:
            break
        rows, columns, determinant = select_minor_modular(
            dense_integer, rank, coefficient_prime)
        determinant_gcd = math.gcd(determinant_gcd, abs(determinant))
        candidates.append(candidate_record(
            "mod_%d" % coefficient_prime, rows, columns, determinant))
    return {
        "prime": prime,
        "vertices": vertices,
        "edges": int(d1.shape[1]),
        "cells": int(d1.shape[0]),
        "rank": rank,
        "trials_requested": trials,
        "minors_completed": len(candidates),
        "determinant_gcd": str(determinant_gcd),
        "saturation_certified": determinant_gcd == 1,
        "minors": candidates,
        "elapsed_s": round(time.time() - started, 3),
    }


def verify_certificate(path):
    with open(path, "r", encoding="utf-8") as stream:
        certificate = json.load(stream)
    prime = int(certificate["prime"])
    _names, vertices, _d0, d1 = coboundaries(prime)
    rank = d1.shape[1] - (vertices - 1)
    if rank != int(certificate["rank"]):
        raise AssertionError("certificate rank does not match chart")
    dense_integer = d1.toarray().astype(np.int64)
    determinant_gcd = 0
    verified = []
    for candidate in certificate["minors"]:
        rows = np.asarray(candidate["row_indices"], dtype=np.int64)
        columns = np.asarray(candidate["column_indices"], dtype=np.int64)
        if len(rows) != rank or len(columns) != rank:
            raise AssertionError("minor has the wrong dimension")
        determinant = int(fmpz_mat(
            dense_integer[np.ix_(rows, columns)].tolist()).det())
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
        "prime": prime,
        "rank": rank,
        "verified_minors": verified,
        "determinant_gcd": str(determinant_gcd),
        "saturation_certified": determinant_gcd == 1,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", type=int, nargs="+")
    parser.add_argument("--trials", type=int, default=1)
    parser.add_argument("--modular-primes", type=int, nargs="+", default=())
    parser.add_argument("--verify")
    args = parser.parse_args()
    if args.verify:
        print(json.dumps(verify_certificate(args.verify)))
        return
    if not args.primes:
        parser.error("--primes is required unless --verify is used")
    for prime in args.primes:
        print(json.dumps(run(prime, args.trials, args.modular_primes)),
              flush=True)


if __name__ == "__main__":
    main()
