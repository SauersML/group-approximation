"""Export the pivot-guided projective harmonic solve for SpaSM.

The Shapiro boundary files use row-vector chain conventions

    d2 : C2 -> C1,       d3 : C3 -> C2.

At level 53 the harmonic plane is the right kernel of ``[d2^T; d3]``.
``sl3_projective_harmonic_modular.py`` records independent row profiles and
two numerically well-conditioned free cell coordinates.  This exporter turns
that certificate into the square systems used by SpaSM:

    X A = B,

where ``A`` is the transpose of the pivot-guided constraint matrix and the
two rows of ``B`` fix the two free coordinates.  SpaSM's solve command uses
this row-vector convention.  Duplicate cellular entries are combined exactly
modulo the requested prime before writing SMS files.

The script performs only streaming integer assembly and file export.  It does
not invoke SpaSM or make any probabilistic algebra claim.
"""

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np


def load_profile(path):
    with np.load(path) as archive:
        stored_characteristic = int(archive["characteristic"][0])
        free_columns = tuple(int(value) for value in archive["free_columns"])
        top_rows = tuple(int(value) for value in archive["top_rows"])
        bottom_rows = tuple(int(value) for value in archive["bottom_rows"])
    return stored_characteristic, free_columns, top_rows, bottom_rows


def read_header(stream, label):
    raw = stream.readline()
    if not raw:
        raise ValueError(f"{label} is empty")
    rows, columns = map(int, raw.split())
    return rows, columns


def add_entry(entries, key, value, characteristic):
    residue = (entries.get(key, 0) + value) % characteristic
    if residue:
        entries[key] = residue
    elif key in entries:
        del entries[key]


def assemble(d2_path, d3_path, profile_path, characteristic):
    profile_characteristic, free_columns, top_rows, bottom_rows = load_profile(
        profile_path)
    if len(set(free_columns)) != len(free_columns):
        raise ValueError("free coordinates are not distinct")

    top_position = {row: index for index, row in enumerate(top_rows)}
    bottom_position = {row: index for index, row in enumerate(bottom_rows)}

    entries = {}
    with open(d2_path, "r", encoding="ascii") as stream:
        cells, edges = read_header(stream, "d2")
        for raw in stream:
            cell, edge, value = map(int, raw.split())
            row = top_position.get(edge)
            if row is not None:
                add_entry(entries, (row, cell), value, characteristic)

    with open(d3_path, "r", encoding="ascii") as stream:
        three_cells, d3_cells = read_header(stream, "d3")
        if d3_cells != cells:
            raise ValueError("boundary dimensions do not compose")
        row_offset = len(top_rows)
        for raw in stream:
            three_cell, cell, value = map(int, raw.split())
            local_row = bottom_position.get(three_cell)
            if local_row is not None:
                add_entry(
                    entries, (row_offset + local_row, cell), value,
                    characteristic)

    rank = len(top_rows) + len(bottom_rows)
    if rank + len(free_columns) != cells:
        raise ValueError("profile does not have the expected nullity")
    remaining = tuple(
        cell for cell in range(cells) if cell not in set(free_columns))
    column_position = {cell: index for index, cell in enumerate(remaining)}

    square = {}
    right_hand_side = {}
    free_position = {cell: index for index, cell in enumerate(free_columns)}
    for (row, cell), value in entries.items():
        column = column_position.get(cell)
        if column is not None:
            # SpaSM solves X A = B, hence export A=M^T.
            square[(column, row)] = value
            continue
        rhs_row = free_position[cell]
        right_hand_side[(rhs_row, row)] = (-value) % characteristic

    if rank != len(remaining):
        raise ValueError("pivot-guided matrix is not square")
    return {
        "cells": cells,
        "edges": edges,
        "three_cells": three_cells,
        "rank": rank,
        "free_columns": free_columns,
        "profile_characteristic": profile_characteristic,
        "top_rank": len(top_rows),
        "bottom_rank": len(bottom_rows),
        "square": square,
        "right_hand_side": right_hand_side,
    }


def write_sms(path, rows, columns, entries):
    digest = hashlib.sha256()
    with open(path, "w", encoding="ascii") as stream:
        header = f"{rows} {columns} M\n"
        stream.write(header)
        digest.update(header.encode("ascii"))
        for (row, column), value in sorted(entries.items()):
            raw = f"{row + 1} {column + 1} {value}\n"
            stream.write(raw)
            digest.update(raw.encode("ascii"))
        marker = "0 0 0\n"
        stream.write(marker)
        digest.update(marker.encode("ascii"))
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--d2", required=True)
    parser.add_argument("--d3", required=True)
    parser.add_argument("--profile", required=True)
    parser.add_argument("--characteristic", type=int, default=101)
    parser.add_argument("--matrix-output", required=True)
    parser.add_argument("--rhs-output", required=True)
    parser.add_argument("--metadata-output")
    args = parser.parse_args()
    if args.characteristic <= 2:
        parser.error("SpaSM export requires an odd prime")

    result = assemble(
        args.d2, args.d3, args.profile, args.characteristic)
    matrix_hash = write_sms(
        args.matrix_output, result["rank"], result["rank"],
        result["square"])
    rhs_hash = write_sms(
        args.rhs_output, len(result["free_columns"]), result["rank"],
        result["right_hand_side"])
    metadata = {
        "coefficient_characteristic": args.characteristic,
        "profile_characteristic": result["profile_characteristic"],
        "chain_dimensions": [
            result["edges"], result["cells"], result["three_cells"]],
        "top_rank": result["top_rank"],
        "bottom_rank": result["bottom_rank"],
        "harmonic_nullity": len(result["free_columns"]),
        "free_columns": list(result["free_columns"]),
        "square_dimension": result["rank"],
        "square_nnz": len(result["square"]),
        "rhs_nnz": len(result["right_hand_side"]),
        "matrix_sha256": matrix_hash,
        "rhs_sha256": rhs_hash,
    }
    rendered = json.dumps(metadata, indent=2, sort_keys=True) + "\n"
    if args.metadata_output:
        Path(args.metadata_output).write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
