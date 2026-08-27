"""Extract a modular basis of the projective-chart harmonic two-plane.

The Shapiro exports use row-vector chain conventions

    d2 : C2 -> C1,       d3 : C3 -> C2.

Over characteristic zero the harmonic plane is the kernel of the stacked
matrix ``[d2^T; d3]``.  At projective level 53 this stack has 28,630
columns and nullity two.  Rather than echelonizing all 68,712 constraint
rows together, this script:

1. extracts independent rows of ``d2^T`` and ``d3`` separately;
2. chooses two free coordinates from a numerical harmonic basis;
3. solves one square sparse system over a prime field;
4. verifies the resulting two vectors against both full boundaries.

The result is a modular reconstruction primitive for the rational pullback
in ``notes/TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md``.  A successful
run writes the two residue vectors to a compressed NumPy archive and emits
a small hash-bearing JSON certificate.
"""

import argparse
import hashlib
import json
import sys
import time

import numpy as np
from scipy.linalg import qr
from sage.all import GF, matrix


def read_sparse(path, field):
    digest = hashlib.sha256()
    entries = {}
    with open(path, "rb") as stream:
        header = stream.readline()
        digest.update(header)
        rows, columns = map(int, header.split())
        for raw in stream:
            digest.update(raw)
            row, column, value = map(int, raw.split())
            key = (row, column)
            entries[key] = entries.get(key, 0) + value
    reduced = {
        key: field(value) for key, value in entries.items()
        if field(value) != 0
    }
    return matrix(field, rows, columns, reduced, sparse=True), digest.hexdigest()


def numerical_free_columns(path, expected_nullity):
    with np.load(path) as archive:
        harmonic = np.asarray(archive["harmonic"][:, :expected_nullity],
                              dtype=np.float64)
    if harmonic.shape[1] != expected_nullity:
        raise AssertionError("numerical archive has too few harmonic vectors")
    _orthogonal, _triangular, pivots = qr(
        harmonic.T, pivoting=True, mode="economic")
    columns = [int(value) for value in pivots[:expected_nullity]]
    if np.linalg.matrix_rank(harmonic[columns, :]) != expected_nullity:
        raise AssertionError("selected free-coordinate block is singular")
    return columns


def matrix_digest(values):
    digest = hashlib.sha256()
    digest.update(np.asarray(values, dtype="<i8").tobytes(order="C"))
    return digest.hexdigest()


def progress(started, message):
    print("%.3fs %s" % (time.perf_counter() - started, message),
          file=sys.stderr, flush=True)


def write_pivot_text(path, characteristic, free_columns, top_rows,
                     bottom_rows):
    with open(path, "w", encoding="ascii") as stream:
        stream.write("%d\n" % characteristic)
        stream.write("%s\n" % " ".join(map(str, free_columns)))
        stream.write("%d\n" % len(top_rows))
        stream.write("%s\n" % " ".join(map(str, top_rows)))
        stream.write("%d\n" % len(bottom_rows))
        stream.write("%s\n" % " ".join(map(str, bottom_rows)))


def run(chart_prime, prefix, numerical_path, characteristic, expected_nullity,
        residue_output, pivot_input, pivot_output, pivot_text_output,
        operation):
    started = time.perf_counter()
    field = GF(characteristic)
    d2, d2_hash = read_sparse(prefix + "-d2.tsv", field)
    d3, d3_hash = read_sparse(prefix + "-d3.tsv", field)
    progress(started, "loaded sparse boundaries")
    if d3.ncols() != d2.nrows():
        raise AssertionError("boundary dimensions do not compose")
    cells = d2.nrows()
    free_columns = numerical_free_columns(numerical_path, expected_nullity)

    top = d2.transpose()
    if pivot_input:
        with np.load(pivot_input) as archive:
            stored_characteristic = int(archive["characteristic"][0])
            if stored_characteristic != characteristic:
                raise AssertionError("pivot characteristic does not match")
            top_rows = tuple(int(value) for value in archive["top_rows"])
            bottom_rows = tuple(
                int(value) for value in archive["bottom_rows"])
            stored_free = [int(value) for value in archive["free_columns"]]
            if stored_free != free_columns:
                raise AssertionError("pivot and numerical free columns differ")
        progress(started, "loaded stored row profiles")
    else:
        top_rows = tuple(int(value) for value in top.pivot_rows())
        progress(started, "selected d2 transpose row profile")
        bottom_rows = tuple(int(value) for value in d3.pivot_rows())
        progress(started, "selected d3 row profile")
    expected_rank = cells - expected_nullity
    if len(top_rows) + len(bottom_rows) != expected_rank:
        raise AssertionError(
            "separate boundary ranks do not give the expected nullity")

    if pivot_output:
        np.savez_compressed(
            pivot_output,
            characteristic=np.asarray([characteristic], dtype=np.int64),
            free_columns=np.asarray(free_columns, dtype=np.int64),
            top_rows=np.asarray(top_rows, dtype=np.int64),
            bottom_rows=np.asarray(bottom_rows, dtype=np.int64),
        )
    if pivot_text_output:
        write_pivot_text(
            pivot_text_output, characteristic, free_columns, top_rows,
            bottom_rows)
    if operation == "pivots":
        return {
            "chart": "projective",
            "chart_prime": chart_prime,
            "coefficient_characteristic": characteristic,
            "chain_dimensions": [d2.ncols(), cells, d3.nrows()],
            "d2_sha256": d2_hash,
            "d3_sha256": d3_hash,
            "d2_rank": len(top_rows),
            "d3_rank": len(bottom_rows),
            "harmonic_nullity_expected": expected_nullity,
            "free_columns": free_columns,
            "pivot_output": pivot_output,
            "pivot_text_output": pivot_text_output,
            "elapsed_seconds": time.perf_counter() - started,
        }

    constraints = top.matrix_from_rows(top_rows).stack(
        d3.matrix_from_rows(bottom_rows))
    square = constraints.delete_columns(sorted(free_columns))
    if square.nrows() != square.ncols():
        raise AssertionError("pivot-guided system is not square")
    progress(started, "assembled square pivot-guided system")
    if operation == "rank":
        square_rank = int(square.rank())
        progress(started, "computed square modular rank")
        return {
            "chart": "projective",
            "chart_prime": chart_prime,
            "coefficient_characteristic": characteristic,
            "square_dimension": square.nrows(),
            "square_nnz": len(square.dict()),
            "square_rank": square_rank,
            "square_nonsingular": square_rank == square.nrows(),
            "free_columns": free_columns,
            "elapsed_seconds": time.perf_counter() - started,
        }
    right_hand_side = -constraints.matrix_from_columns(free_columns)
    solved = square.solve_right(right_hand_side)
    progress(started, "solved square modular system")

    free_set = set(free_columns)
    remaining = [index for index in range(cells) if index not in free_set]
    kernel = matrix(field, cells, expected_nullity, sparse=True)
    for column, coordinate in enumerate(free_columns):
        kernel[coordinate, column] = 1
    for row, coordinate in enumerate(remaining):
        for column in range(expected_nullity):
            value = solved[row, column]
            if value:
                kernel[coordinate, column] = value

    if top * kernel != 0:
        raise AssertionError("modular vectors fail the cycle equations")
    if d3 * kernel != 0:
        raise AssertionError("modular vectors fail the cocycle equations")
    if kernel.matrix_from_rows(free_columns) != matrix.identity(
            field, expected_nullity):
        raise AssertionError("free-coordinate normalization failed")

    residues = np.empty((cells, expected_nullity), dtype=np.int64)
    for row in range(cells):
        for column in range(expected_nullity):
            residues[row, column] = int(kernel[row, column])
    np.savez_compressed(
        residue_output,
        residues=residues,
        characteristic=np.asarray([characteristic], dtype=np.int64),
        free_columns=np.asarray(free_columns, dtype=np.int64),
    )
    return {
        "chart": "projective",
        "chart_prime": chart_prime,
        "coefficient_characteristic": characteristic,
        "chain_dimensions": [d2.ncols(), cells, d3.nrows()],
        "d2_sha256": d2_hash,
        "d3_sha256": d3_hash,
        "d2_rank": len(top_rows),
        "d3_rank": len(bottom_rows),
        "harmonic_nullity": expected_nullity,
        "free_columns": free_columns,
        "full_boundary_verification": True,
        "residue_sha256": matrix_digest(residues),
        "residue_output": residue_output,
        "elapsed_seconds": time.perf_counter() - started,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--chart-prime", type=int, required=True)
    parser.add_argument("--prefix", required=True)
    parser.add_argument("--numerical", required=True)
    parser.add_argument("--characteristic", type=int, default=101)
    parser.add_argument("--expected-nullity", type=int, default=2)
    parser.add_argument("--residue-output")
    parser.add_argument("--pivot-input")
    parser.add_argument("--pivot-output")
    parser.add_argument("--pivot-text-output")
    parser.add_argument(
        "--operation", choices=("pivots", "rank", "solve"), required=True)
    args = parser.parse_args()
    if args.characteristic <= 2:
        parser.error("--characteristic must be an odd prime")
    if args.expected_nullity <= 0:
        parser.error("--expected-nullity must be positive")
    if args.operation == "solve" and not args.residue_output:
        parser.error("--residue-output is required for --operation solve")
    if (args.operation == "pivots" and not args.pivot_output
            and not args.pivot_input
            and not args.pivot_text_output):
        parser.error(
            "--operation pivots requires a pivot input or output")
    result = run(
        args.chart_prime, args.prefix, args.numerical, args.characteristic,
        args.expected_nullity, args.residue_output, args.pivot_input,
        args.pivot_output, args.pivot_text_output, args.operation)
    print(json.dumps(result, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
