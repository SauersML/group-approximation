"""Hensel-lift compact harmonic cycles through the full HAP boundary.

This is the higher-carry companion to
``sl3_projective_harmonic_primary_coupling.py``.  It uses the same canonical
compact representatives and the same omitted orientation-torsion variables,
but solves the total cycle equations modulo successive powers of two using
the exact integral HAP boundary.

Run with Sage's Python on MSI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from sage.all import GF, ZZ, Integers, matrix, vector

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_derived_e1 import coordinate_indices, read_boundary
from sl3_projective_harmonic_primary_coupling import (
    compact_representatives,
    read_harmonic_basis,
    signed_torsion_representatives,
)


def centered(value: int, modulus: int) -> int:
    residue = value % modulus
    return residue - modulus if 2 * residue > modulus else residue


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("compact_export", type=Path)
    parser.add_argument("full_prefix", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--depth", type=int, default=4)
    args = parser.parse_args()
    if args.depth < 1:
        raise ValueError("depth must be positive")

    prime, degree, orbit_dimensions, cells = parse(args.compact_export)
    compact_dimensions, _compact_boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    representatives = compact_representatives(degree, cells)
    if len(representatives) != compact_dimensions[2]:
        raise AssertionError("compact representative count is wrong")

    full_boundary = read_boundary(
        Path(str(args.full_prefix) + "-d2.tsv"), ZZ)
    if full_boundary.nrows() != 10 * degree or full_boundary.ncols() != 4 * degree:
        raise AssertionError("unexpected full HAP dimensions")

    cell_generators = (8, 9)
    two_cell_torsion_points = [
        signed_torsion_representatives(degree, cells[(2, cell_index)])
        for cell_index in (1, 2)
    ]
    torsion_indices = [
        cell_generators[cell_index - 1] * degree + point
        for cell_index in (1, 2)
        for point in two_cell_torsion_points[cell_index - 1]
    ]
    correction_indices = (
        torsion_indices
        + coordinate_indices(2, 1, degree)
        + coordinate_indices(2, 0, degree)
    )
    correction_boundary = full_boundary.matrix_from_rows(correction_indices)
    correction_mod_two = correction_boundary.change_ring(GF(2))

    harmonic_rows = read_harmonic_basis(
        args.harmonic_basis, compact_dimensions[2])
    right_sides = []
    for integer_row in harmonic_rows:
        compact_lift = vector(ZZ, full_boundary.nrows())
        for compact_coordinate, coefficient in enumerate(integer_row):
            if coefficient == 0:
                continue
            cell_index, point, source_sign = representatives[compact_coordinate]
            generator = cell_generators[cell_index - 1]
            compact_lift[generator * degree + point] += source_sign * coefficient
        right_sides.append(-(compact_lift * full_boundary))

    solutions = [vector(ZZ, len(correction_indices)) for _ in harmonic_rows]
    records = []
    for level in range(args.depth):
        scale = 1 << level
        bit_right_sides = []
        for basis_index, right_side in enumerate(right_sides):
            residual = right_side - solutions[basis_index] * correction_boundary
            if any(int(value) % scale for value in residual):
                raise AssertionError("Hensel residual lost divisibility")
            bit_right_sides.append(vector(
                GF(2), [ZZ(value // scale) for value in residual]))
        try:
            bit_solutions = correction_mod_two.solve_left(
                matrix(GF(2), bit_right_sides))
        except ValueError:
            modulus = 2 * scale
            residue_ring = Integers(modulus)
            try:
                direct_solutions = correction_boundary.change_ring(
                    residue_ring).solve_left(matrix(residue_ring, right_sides))
            except Exception as error:
                records.append({
                    "level": level + 1,
                    "modulus": modulus,
                    "solvable": None,
                    "greedy_hensel_solvable": False,
                    "direct_ring_solve_error": type(error).__name__ + ": " + str(error),
                })
                break
            solutions = [
                vector(ZZ, [ZZ(value) for value in direct_solutions.row(row)])
                for row in range(len(harmonic_rows))
            ]
            records.append({
                "level": level + 1,
                "modulus": modulus,
                "solvable": True,
                "greedy_hensel_solvable": False,
                "direct_ring_solve": True,
                "correction_supports": [
                    len(solution.support()) for solution in solutions
                ],
                "centered_correction_squared_norms": [
                    sum(centered(int(value), modulus) ** 2 for value in solution)
                    for solution in solutions
                ],
                "centered_maximum_absolute_coefficients": [
                    max(abs(centered(int(value), modulus)) for value in solution)
                    for solution in solutions
                ],
            })
            continue
        for basis_index in range(len(harmonic_rows)):
            solutions[basis_index] += scale * vector(
                ZZ, bit_solutions.row(basis_index))
        modulus = 2 * scale
        if any(
            any(int(value) % modulus for value in (
                right_sides[basis_index]
                - solutions[basis_index] * correction_boundary))
            for basis_index in range(len(harmonic_rows))
        ):
            raise AssertionError("invalid Hensel correction")
        records.append({
            "level": level + 1,
            "modulus": modulus,
            "solvable": True,
            "greedy_hensel_solvable": True,
            "correction_supports": [
                len(solution.support()) for solution in solutions
            ],
            "centered_correction_squared_norms": [
                sum(centered(int(value), modulus) ** 2 for value in solution)
                for solution in solutions
            ],
            "centered_maximum_absolute_coefficients": [
                max(abs(centered(int(value), modulus)) for value in solution)
                for solution in solutions
            ],
        })

    payload = {
        "prime": prime,
        "projective_degree": degree,
        "requested_depth": args.depth,
        "reached_depth": sum(record["solvable"] is True for record in records),
        "compact_degree_two_dimension": compact_dimensions[2],
        "full_degree_two_dimension": full_boundary.nrows(),
        "correction_variable_count": len(correction_indices),
        "two_cell_orientation_torsion_orbits": [
            len(points) for points in two_cell_torsion_points
        ],
        "records": records,
    }
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    print("sha256=" + hashlib.sha256(encoded.encode("utf-8")).hexdigest())


if __name__ == "__main__":
    main()
