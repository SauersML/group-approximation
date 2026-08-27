"""Find and exactly verify higher binary harmonic lifts by sparse MILP.

For a modulus ``m=2^k`` the congruence ``x A = b (mod m)`` is written as
the integral feasibility system ``A^T x - m y = b`` with bounded residue
variables ``0 <= x_i < m``.  HiGHS is used only to find a candidate; every
reported solution is multiplied by the exact Sage integer boundary and
verified coordinatewise modulo ``m``.

Run with Sage's Python on MSI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix, hstack
from sage.all import ZZ, vector

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_derived_e1 import coordinate_indices, read_boundary
from sl3_projective_harmonic_primary_coupling import (
    compact_representatives,
    read_harmonic_basis,
    signed_torsion_representatives,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("compact_export", type=Path)
    parser.add_argument("full_prefix", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--modulus", type=int, default=8)
    parser.add_argument("--time-limit", type=float, default=600.0)
    args = parser.parse_args()
    if args.modulus < 2 or args.modulus & (args.modulus - 1):
        raise ValueError("modulus must be a positive power of two")

    prime, degree, orbit_dimensions, cells = parse(args.compact_export)
    compact_dimensions, _compact_boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    representatives = compact_representatives(degree, cells)
    full_boundary = read_boundary(
        Path(str(args.full_prefix) + "-d2.tsv"), ZZ)

    cell_generators = (8, 9)
    two_cell_torsion_points = [
        signed_torsion_representatives(degree, cells[(2, cell_index)])
        for cell_index in (1, 2)
    ]
    correction_indices = [
        cell_generators[cell_index - 1] * degree + point
        for cell_index in (1, 2)
        for point in two_cell_torsion_points[cell_index - 1]
    ] + coordinate_indices(2, 1, degree) + coordinate_indices(2, 0, degree)
    correction_boundary = full_boundary.matrix_from_rows(correction_indices)
    variable_count = correction_boundary.nrows()
    equation_count = correction_boundary.ncols()

    entries = correction_boundary.dict()
    coefficient_matrix = coo_matrix(
        (
            np.fromiter((int(value) for value in entries.values()), dtype=np.float64),
            (
                np.fromiter((column for _row, column in entries), dtype=np.int32),
                np.fromiter((row for row, _column in entries), dtype=np.int32),
            ),
        ),
        shape=(equation_count, variable_count),
    ).tocsr()
    carry_matrix = -args.modulus * coo_matrix(
        (
            np.ones(equation_count),
            (np.arange(equation_count), np.arange(equation_count)),
        ),
        shape=(equation_count, equation_count),
    ).tocsr()
    system = hstack((coefficient_matrix, carry_matrix), format="csr")
    total_variables = variable_count + equation_count
    lower = np.concatenate((
        np.zeros(variable_count),
        np.full(equation_count, -1000.0),
    ))
    upper = np.concatenate((
        np.full(variable_count, float(args.modulus - 1)),
        np.full(equation_count, 1000.0),
    ))
    bounds = Bounds(lower, upper)
    integrality = np.ones(total_variables, dtype=np.uint8)
    objective = np.zeros(total_variables)

    harmonic_rows = read_harmonic_basis(
        args.harmonic_basis, compact_dimensions[2])
    records = []
    for basis_index, integer_row in enumerate(harmonic_rows):
        compact_lift = vector(ZZ, full_boundary.nrows())
        for compact_coordinate, coefficient in enumerate(integer_row):
            if coefficient == 0:
                continue
            cell_index, point, source_sign = representatives[compact_coordinate]
            generator = cell_generators[cell_index - 1]
            compact_lift[generator * degree + point] += source_sign * coefficient
        right_side = -(compact_lift * full_boundary)
        residue = np.array(
            [int(value) % args.modulus for value in right_side],
            dtype=np.float64,
        )
        result = milp(
            objective,
            integrality=integrality,
            bounds=bounds,
            constraints=LinearConstraint(system, residue, residue),
            options={
                "time_limit": args.time_limit,
                "presolve": True,
            },
        )
        record = {
            "basis_index": basis_index,
            "status": int(result.status),
            "message": result.message,
            "success": bool(result.success),
        }
        if result.x is not None:
            correction = vector(
                ZZ,
                [int(round(value)) % args.modulus
                 for value in result.x[:variable_count]],
            )
            residual = correction * correction_boundary - right_side
            verified = all(int(value) % args.modulus == 0 for value in residual)
            record.update({
                "exact_congruence_verified": verified,
                "correction_support": len(correction.support()),
                "maximum_residue": max(map(int, correction)),
            })
            if not verified:
                raise AssertionError("MILP candidate failed exact verification")
        records.append(record)

    payload = {
        "prime": prime,
        "projective_degree": degree,
        "modulus": args.modulus,
        "correction_variable_count": variable_count,
        "equation_count": equation_count,
        "system_nonzeros": int(system.nnz),
        "records": records,
    }
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    print("sha256=" + hashlib.sha256(encoded.encode("utf-8")).hexdigest())


if __name__ == "__main__":
    main()
