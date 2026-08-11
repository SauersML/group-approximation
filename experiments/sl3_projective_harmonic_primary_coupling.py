"""Lift compact projective harmonic cycles through the filtered HAP complex.

The compact cellular complex is the zero vertical row of HAP's Wall total
complex.  Its two degree-two cells are the last two free generators of total
degree two.  A signed-coinvariant cycle therefore has a canonical sparse
lift obtained by choosing one coefficient point in every orbit.  This script
cancels the resulting positive-filtration syndrome, first in bidegree
``(1,1)`` and then in ``(0,2)``, over a specified prime field.

Run with Sage's Python.  The full boundary prefix is the prefix passed to
``sl3_projective_h2_export.g``; only ``-d2.tsv`` is needed here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from sage.all import GF, vector

from sl3_projective_cellular_analyze import build_boundaries, coinvariants, parse
from sl3_projective_derived_e1 import coordinate_indices, read_boundary


def read_harmonic_basis(path: Path, dimension: int):
    rows = []
    with path.open(encoding="ascii") as stream:
        header = stream.readline().split()
        if not header or header[0] != "coordinate":
            raise ValueError("invalid harmonic basis header")
        rank = len(header) - 1
        rows = [[] for _ in range(rank)]
        for expected_coordinate, line in enumerate(stream):
            fields = line.split()
            if int(fields[0]) != expected_coordinate:
                raise ValueError("harmonic coordinates are not consecutive")
            if len(fields) != rank + 1:
                raise ValueError("invalid harmonic basis row")
            for basis_index, value in enumerate(fields[1:]):
                rows[basis_index].append(int(value))
    if any(len(row) != dimension for row in rows):
        raise ValueError("harmonic basis has the wrong ambient dimension")
    return rows


def compact_representatives(degree: int, cells):
    """Return one coefficient point for every compact degree-two coordinate."""

    representatives = []
    for cell_index in (1, 2):
        dimension, coordinate_map = coinvariants(degree, cells[(2, cell_index)])
        local_representatives = [None] * dimension
        for point, value in enumerate(coordinate_map):
            if value is None:
                continue
            coordinate, _sign = value
            if local_representatives[coordinate] is None:
                local_representatives[coordinate] = point
        if any(point is None for point in local_representatives):
            raise AssertionError("coinvariant coordinate has no representative")
        representatives.extend(
            (8 + cell_index - 1, point)
            for point in local_representatives
        )
    return representatives


def solve_filtered_lift(boundary, degree: int, compact_lift):
    field = boundary.base_ring()
    target_q1 = coordinate_indices(1, 1, degree)
    target_q0 = coordinate_indices(1, 0, degree)
    source_q1 = coordinate_indices(2, 1, degree)
    source_q0 = coordinate_indices(2, 0, degree)

    initial_boundary = compact_lift * boundary
    q1_syndrome = initial_boundary[target_q1]
    q1_block = boundary.matrix_from_rows_and_columns(source_q1, target_q1)
    try:
        q1_local = q1_block.solve_left(-q1_syndrome)
    except ValueError:
        return {"q1_solvable": False}

    q1_correction = vector(field, boundary.nrows())
    for local, total in enumerate(source_q1):
        q1_correction[total] = q1_local[local]
    after_q1 = (compact_lift + q1_correction) * boundary
    if any(after_q1[index] for index in target_q1):
        raise AssertionError("q=1 correction left a q=1 residual")

    q0_syndrome = after_q1[target_q0]
    q0_block = boundary.matrix_from_rows_and_columns(source_q0, target_q0)
    try:
        q0_local = q0_block.solve_left(-q0_syndrome)
    except ValueError:
        return {
            "q1_solvable": True,
            "q0_solvable": False,
            "q1_correction_support": len(q1_local.support()),
            "q0_syndrome_support": len(q0_syndrome.support()),
        }

    q0_correction = vector(field, boundary.nrows())
    for local, total in enumerate(source_q0):
        q0_correction[total] = q0_local[local]
    total_lift = compact_lift + q1_correction + q0_correction
    if total_lift * boundary:
        raise AssertionError("filtered correction is not a total cycle")

    first_q0 = q0_local[:degree]
    return {
        "q1_solvable": True,
        "q0_solvable": True,
        "compact_support": len(compact_lift.support()),
        "q1_syndrome_support": len(q1_syndrome.support()),
        "q1_correction_support": len(q1_local.support()),
        "q0_syndrome_support": len(q0_syndrome.support()),
        "q0_correction_support": len(q0_local.support()),
        "total_lift_support": len(total_lift.support()),
        "first_q0_generator_support": len(first_q0.support()),
        "first_q0_generator_coordinates": list(first_q0.support()),
        "exceptional_singleton_coefficient": int(first_q0[0]),
        "ordinary_singleton_coefficient": int(first_q0[1]),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("compact_export", type=Path)
    parser.add_argument("full_prefix", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--characteristic", type=int, default=2)
    args = parser.parse_args()

    prime, degree, orbit_dimensions, cells = parse(args.compact_export)
    compact_dimensions, compact_boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    representatives = compact_representatives(degree, cells)
    if len(representatives) != compact_dimensions[2]:
        raise AssertionError("compact representative count is wrong")

    field = GF(args.characteristic)
    full_boundary = read_boundary(
        Path(str(args.full_prefix) + "-d2.tsv"), field)
    if full_boundary.nrows() != 10 * degree or full_boundary.ncols() != 4 * degree:
        raise AssertionError("unexpected full HAP dimensions")

    harmonic_rows = read_harmonic_basis(
        args.harmonic_basis, compact_dimensions[2])
    compact_boundary = compact_boundaries[2].change_ring(field)
    records = []
    for basis_index, integer_row in enumerate(harmonic_rows):
        compact_cycle = vector(field, integer_row)
        if compact_cycle * compact_boundary:
            raise AssertionError("reduced compact harmonic vector is not a cycle")
        compact_lift = vector(field, full_boundary.nrows())
        for compact_coordinate in compact_cycle.support():
            generator, point = representatives[compact_coordinate]
            compact_lift[generator * degree + point] += compact_cycle[compact_coordinate]
        record = solve_filtered_lift(full_boundary, degree, compact_lift)
        record["basis_index"] = basis_index
        record["compact_reduced_support"] = len(compact_cycle.support())
        records.append(record)

    payload = {
        "prime": prime,
        "projective_degree": degree,
        "characteristic": args.characteristic,
        "compact_degree_two_dimension": compact_dimensions[2],
        "full_degree_two_dimension": full_boundary.nrows(),
        "canonical_representative_count": len(representatives),
        "records": records,
    }
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    print("sha256=" + hashlib.sha256(encoded.encode("utf-8")).hexdigest())


if __name__ == "__main__":
    main()
