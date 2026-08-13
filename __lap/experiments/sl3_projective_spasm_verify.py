"""Verify a SpaSM solution for the projective harmonic two-plane.

The companion exporter writes a row-vector system ``X A = B`` after deleting
the certified free cell coordinates.  This verifier reconstructs the full
cell vectors and checks both original boundary equations entry-by-entry over
the prime field.  A successful run emits the same compressed residue format
used by ``sl3_projective_harmonic_modular.py`` plus a hash-bearing JSON
certificate.
"""

import argparse
import hashlib
import json

import numpy as np


def read_sms(path, characteristic):
    with open(path, "r", encoding="ascii") as stream:
        rows, columns, kind = stream.readline().split()
        if kind != "M":
            raise ValueError("only modular SMS matrices are supported")
        matrix = np.zeros((int(rows), int(columns)), dtype=np.int64)
        for raw in stream:
            row, column, value = map(int, raw.split())
            if row == 0 and column == 0 and value == 0:
                break
            matrix[row - 1, column - 1] = (
                matrix[row - 1, column - 1] + value) % characteristic
    return matrix


def load_profile(path):
    with np.load(path) as archive:
        stored_characteristic = int(archive["characteristic"][0])
        free_columns = tuple(int(value) for value in archive["free_columns"])
    return stored_characteristic, free_columns


def read_header(stream, label):
    raw = stream.readline()
    if not raw:
        raise ValueError(f"{label} is empty")
    return tuple(map(int, raw.split()))


def verify_d2(path, vectors, characteristic):
    with open(path, "r", encoding="ascii") as stream:
        cells, edges = read_header(stream, "d2")
        if cells != vectors.shape[0]:
            raise ValueError("d2 cell dimension does not match solution")
        residual = np.zeros((edges, vectors.shape[1]), dtype=np.int64)
        for raw in stream:
            cell, edge, value = map(int, raw.split())
            residual[edge] += value * vectors[cell]
            residual[edge] %= characteristic
    return int(np.count_nonzero(residual))


def verify_d3(path, vectors, characteristic):
    with open(path, "r", encoding="ascii") as stream:
        rows, cells = read_header(stream, "d3")
        if cells != vectors.shape[0]:
            raise ValueError("d3 cell dimension does not match solution")
        residual = np.zeros((rows, vectors.shape[1]), dtype=np.int64)
        for raw in stream:
            row, cell, value = map(int, raw.split())
            residual[row] += value * vectors[cell]
            residual[row] %= characteristic
    return int(np.count_nonzero(residual))


def residue_digest(vectors):
    digest = hashlib.sha256()
    digest.update(np.asarray(vectors, dtype="<i8").tobytes(order="C"))
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--d2", required=True)
    parser.add_argument("--d3", required=True)
    parser.add_argument("--profile", required=True)
    parser.add_argument("--solution", required=True)
    parser.add_argument("--characteristic", type=int, default=101)
    parser.add_argument("--residue-output", required=True)
    parser.add_argument("--metadata-output")
    args = parser.parse_args()
    if args.characteristic <= 2:
        parser.error("SpaSM verification requires an odd prime")

    profile_characteristic, free_columns = load_profile(args.profile)
    solution = read_sms(args.solution, args.characteristic)
    if solution.shape[0] != len(free_columns):
        raise ValueError("solution row count does not match harmonic nullity")

    cells = solution.shape[1] + len(free_columns)
    free_set = set(free_columns)
    remaining = [cell for cell in range(cells) if cell not in free_set]
    vectors = np.zeros((cells, len(free_columns)), dtype=np.int64)
    vectors[remaining, :] = solution.T
    for column, cell in enumerate(free_columns):
        vectors[cell, column] = 1

    d2_nonzero_residuals = verify_d2(
        args.d2, vectors, args.characteristic)
    d3_nonzero_residuals = verify_d3(
        args.d3, vectors, args.characteristic)
    normalized_free_block = vectors[list(free_columns), :]
    if not np.array_equal(
            normalized_free_block,
            np.eye(len(free_columns), dtype=np.int64)):
        raise AssertionError("free-coordinate normalization failed")
    if d2_nonzero_residuals or d3_nonzero_residuals:
        raise AssertionError("SpaSM vectors fail a full boundary equation")

    np.savez_compressed(
        args.residue_output,
        residues=vectors,
        characteristic=np.asarray([args.characteristic], dtype=np.int64),
        free_columns=np.asarray(free_columns, dtype=np.int64))
    metadata = {
        "coefficient_characteristic": args.characteristic,
        "profile_characteristic": profile_characteristic,
        "cells": cells,
        "harmonic_nullity": len(free_columns),
        "free_columns": list(free_columns),
        "d2_nonzero_residuals": d2_nonzero_residuals,
        "d3_nonzero_residuals": d3_nonzero_residuals,
        "full_boundary_verification": True,
        "residue_sha256": residue_digest(vectors),
    }
    rendered = json.dumps(metadata, indent=2, sort_keys=True) + "\n"
    if args.metadata_output:
        with open(args.metadata_output, "w", encoding="utf-8") as stream:
            stream.write(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
