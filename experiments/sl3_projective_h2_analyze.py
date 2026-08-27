"""Certify rational and modular H2 ranks from exported Shapiro boundaries.

Run this file with SageMath after ``sl3_projective_h2_export.g``.  The GAP
export uses row-vector chain conventions, so the chain identity is
``d3*d2=0`` and

    dim H2(F) = rows(d2) - rank_F(d2) - rank_F(d3).
"""

import argparse
import hashlib
import json
import sys
import time

from sage.all import ChainComplex, GF, QQ, ZZ, matrix


def read_sparse(path, ring):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        raw = stream.read()
    digest.update(raw)
    lines = raw.decode("ascii").splitlines()
    rows, columns = map(int, lines[0].split())
    entries = {}
    for line in lines[1:]:
        row, column, value = map(int, line.split())
        key = (row, column)
        entries[key] = entries.get(key, 0) + value
    entries = {key: ring(value) for key, value in entries.items()
               if ring(value) != 0}
    return matrix(ring, rows, columns, entries, sparse=True), digest.hexdigest()


def field_result(d2_path, d3_path, field, label, chain_check):
    started = time.perf_counter()
    d2, d2_hash = read_sparse(d2_path, field)
    d3, d3_hash = read_sparse(d3_path, field)
    print(
        "%s loaded in %.3fs" % (label, time.perf_counter() - started),
        file=sys.stderr, flush=True)
    if d3.ncols() != d2.nrows():
        raise AssertionError("boundary dimensions do not compose")
    if chain_check == "exact":
        chain_started = time.perf_counter()
        chain = d3 * d2
        if chain != 0:
            raise AssertionError("exported boundaries do not form a chain complex")
        print(
            "%s exact chain check in %.3fs" % (
                label, time.perf_counter() - chain_started),
            file=sys.stderr, flush=True)
    rank_started = time.perf_counter()
    rank2 = d2.rank()
    print(
        "%s d2 rank %d in %.3fs" % (
            label, rank2, time.perf_counter() - rank_started),
        file=sys.stderr, flush=True)
    rank_started = time.perf_counter()
    rank3 = d3.rank()
    print(
        "%s d3 rank %d in %.3fs" % (
            label, rank3, time.perf_counter() - rank_started),
        file=sys.stderr, flush=True)
    dimension = d2.nrows() - rank2 - rank3
    return {
        "field": label,
        "chain_dimensions": [d2.ncols(), d2.nrows(), d3.nrows()],
        "d2_rank": rank2,
        "d3_rank": rank3,
        "h2_dimension": dimension,
        "d2_nnz": len(d2.dict()),
        "d3_nnz": len(d3.dict()),
        "d2_sha256": d2_hash,
        "d3_sha256": d3_hash,
        "chain_check": chain_check,
        "chain_squared_zero": True if chain_check == "exact" else None,
    }


def integral_result(d2_path, d3_path):
    d2, d2_hash = read_sparse(d2_path, ZZ)
    d3, d3_hash = read_sparse(d3_path, ZZ)
    complex_ = ChainComplex(
        {2: d2.transpose(), 3: d3.transpose()}, degree=-1)
    homology = complex_.homology(2)
    return {
        "group": str(homology),
        "abelian_invariants": [int(value) for value in homology.invariants()],
        "d2_sha256": d2_hash,
        "d3_sha256": d3_hash,
    }


def run(prime, prefix, coefficient_primes, include_integral, include_rational,
        chain_check):
    d2_path = prefix + "-d2.tsv"
    d3_path = prefix + "-d3.tsv"
    result = {
        "chart": "projective",
        "chart_prime": prime,
        "method": "HAP_SL3_resolution_plus_Shapiro_permutation_module",
    }
    if include_integral:
        result["integral"] = integral_result(d2_path, d3_path)
    if include_rational:
        result["rational"] = field_result(
            d2_path, d3_path, QQ, "Q", chain_check)
    result["modular"] = [
        field_result(
            d2_path, d3_path, GF(ell), "F_%d" % ell, chain_check)
        for ell in coefficient_primes]
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, required=True)
    parser.add_argument("--prefix", required=True)
    parser.add_argument("--coefficient-primes", type=int, nargs="+",
                        default=(2, 3, 5, 7))
    parser.add_argument("--without-integral", action="store_true")
    parser.add_argument("--without-rational", action="store_true")
    parser.add_argument(
        "--chain-check", choices=("exact", "structural"), default="exact")
    args = parser.parse_args()
    print(json.dumps(run(
        args.prime, args.prefix, args.coefficient_primes,
        not args.without_integral, not args.without_rational,
        args.chain_check)), flush=True)


if __name__ == "__main__":
    main()
