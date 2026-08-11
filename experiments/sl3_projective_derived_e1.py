"""Compute the vertical E1 rows of the projective derived resolution.

Run on MSI after ``sl3_projective_h2_export.g``.  The HAP resolution retains
the Wall bidegree ``(q,s)``.  This script reduces the first three specialized
boundaries modulo two, extracts the vertical blocks preserving ``q``, and
computes the exact E1 homology dimensions in total degree two.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from sage.all import GF, matrix


Q_BY_TOTAL_GENERATOR = {
    0: [0],
    1: [0, 0, 0, 1],
    2: [0, 0, 0, 0, 0, 0, 1, 1, 2, 2],
    3: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3],
}


def read_boundary(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    source_rank, target_rank = map(int, lines[0].split())
    entries = {}
    for line in lines[1:]:
        source, target, coefficient = map(int, line.split())
        key = (source, target)
        entries[key] = (entries.get(key, 0) + coefficient) % 2
    return matrix(
        GF(2),
        source_rank,
        target_rank,
        {key: value for key, value in entries.items() if value},
        sparse=True,
    )


def coordinate_indices(total_degree: int, cellular_degree: int, degree: int):
    return [
        generator * degree + coordinate
        for generator, q in enumerate(Q_BY_TOTAL_GENERATOR[total_degree])
        if q == cellular_degree
        for coordinate in range(degree)
    ]


def vertical_rank(boundaries, total_degree: int, cellular_degree: int, degree: int):
    source = coordinate_indices(total_degree, cellular_degree, degree)
    target = coordinate_indices(total_degree - 1, cellular_degree, degree)
    block = boundaries[total_degree].matrix_from_rows_and_columns(source, target)
    return int(block.rank()), block.nrows(), block.ncols()


def filtered_block(
    boundaries, total_degree: int, source_q: int, target_q: int, degree: int
):
    source = coordinate_indices(total_degree, source_q, degree)
    target = coordinate_indices(total_degree - 1, target_q, degree)
    return boundaries[total_degree].matrix_from_rows_and_columns(source, target)


def horizontal_h1_rank(boundaries, degree: int):
    """Rank of E1_(1,1) -> E1_(0,1), modulo vertical boundaries."""

    source_vertical_out = filtered_block(boundaries, 2, 1, 1, degree)
    source_vertical_in = filtered_block(boundaries, 3, 1, 1, degree)
    target_vertical_out = filtered_block(boundaries, 1, 0, 0, degree)
    target_vertical_in = filtered_block(boundaries, 2, 0, 0, degree)
    horizontal = filtered_block(boundaries, 2, 1, 0, degree)

    source_cycles = source_vertical_out.left_kernel().basis_matrix()
    if source_vertical_in * source_vertical_out:
        raise AssertionError("source vertical boundaries are not cycles")
    images = source_cycles * horizontal
    if images * target_vertical_out:
        raise AssertionError("horizontal images are not target vertical cycles")

    induced_rank = int(target_vertical_in.stack(images).rank()) \
        - int(target_vertical_in.rank())
    source_h1 = source_vertical_out.nrows() \
        - int(source_vertical_out.rank()) - int(source_vertical_in.rank())
    target_h1 = target_vertical_out.nrows() \
        - int(target_vertical_out.rank()) - int(target_vertical_in.rank())
    return {
        "source_dimension": source_h1,
        "target_dimension": target_h1,
        "rank": induced_rank,
        "kernel_dimension": source_h1 - induced_rank,
        "cokernel_dimension": target_h1 - induced_rank,
    }


def horizontal_image_rank(
    boundaries, total_degree: int, source_q: int, target_q: int, degree: int
):
    """Rank on E1 without needing the next source vertical boundary."""

    source_vertical_out = filtered_block(
        boundaries, total_degree, source_q, source_q, degree)
    target_vertical_out = filtered_block(
        boundaries, total_degree - 1, target_q, target_q, degree)
    target_vertical_in = filtered_block(
        boundaries, total_degree, target_q, target_q, degree)
    horizontal = filtered_block(
        boundaries, total_degree, source_q, target_q, degree)

    source_cycles = source_vertical_out.left_kernel().basis_matrix()
    images = source_cycles * horizontal
    if images * target_vertical_out:
        raise AssertionError("horizontal images are not target vertical cycles")
    return int(target_vertical_in.stack(images).rank()) \
        - int(target_vertical_in.rank())


def analyze(prime: int, prefix: Path):
    degree = prime**2 + prime + 1
    boundaries = {
        total_degree: read_boundary(
            Path(f"{prefix}-d{total_degree}.tsv"))
        for total_degree in range(1, 4)
    }
    vertical = {}
    for total_degree in range(1, 4):
        for cellular_degree in range(total_degree):
            rank, source, target = vertical_rank(
                boundaries, total_degree, cellular_degree, degree)
            vertical[(cellular_degree, total_degree - cellular_degree)] = {
                "rank": rank,
                "source_dimension": source,
                "target_dimension": target,
            }

    e1_total_two = {}
    for cellular_degree in range(3):
        stabilizer_degree = 2 - cellular_degree
        chain_dimension = len([
            q for q in Q_BY_TOTAL_GENERATOR[2] if q == cellular_degree
        ]) * degree
        outgoing = vertical[(cellular_degree, stabilizer_degree)]["rank"] \
            if stabilizer_degree > 0 else 0
        incoming = vertical[(cellular_degree, stabilizer_degree + 1)]["rank"]
        e1_total_two[f"{cellular_degree},{stabilizer_degree}"] = (
            chain_dimension - outgoing - incoming
        )

    outgoing_h1 = horizontal_h1_rank(boundaries, degree)
    incoming_h1_rank = horizontal_image_rank(
        boundaries, total_degree=3, source_q=2, target_q=1, degree=degree)
    e2_1_1 = e1_total_two["1,1"] - outgoing_h1["rank"] - incoming_h1_rank
    if e2_1_1 < 0:
        raise AssertionError("horizontal E1 ranks violate the chain inequality")

    return {
        "prime": prime,
        "projective_degree": degree,
        "vertical_blocks": {
            f"{q},{s}": value for (q, s), value in sorted(vertical.items())
        },
        "E1_total_degree_two_dimensions": e1_total_two,
        "E1_horizontal_H1_D8_to_H1_S4": outgoing_h1,
        "E1_horizontal_H1_cells_to_D8_image_rank": incoming_h1_rank,
        "E2_1_1_dimension": e2_1_1,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("prime", type=int)
    parser.add_argument("prefix", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    result = analyze(args.prime, args.prefix)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
