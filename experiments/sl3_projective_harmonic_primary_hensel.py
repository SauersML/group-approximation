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
import heapq
import hashlib
import json
import time
from pathlib import Path

from sage.all import GF, ZZ, matrix, vector

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


def solve_power_of_two_left(boundary, right_sides, modulus, time_limit):
    """Solve all ``x * boundary = right_side`` systems modulo ``modulus``.

    Unit-pivot elimination over ``Z/2^k`` leaves a system whose coefficients
    are all even.  Dividing that residual system and its right side by two is
    an equivalent system over ``Z/2^(k-1)``.  Recursing gives exact module
    elimination without a field-only composite-ring backend.
    """
    if modulus < 2 or modulus & (modulus - 1):
        raise ValueError("modulus must be a positive power of two")
    started = time.monotonic()
    variable_count = boundary.nrows()
    equation_count = boundary.ncols()
    right_side_count = len(right_sides)
    equations = [dict() for _ in range(equation_count)]
    for (variable_index, equation_index), coefficient in boundary.dict().items():
        residue = int(coefficient) % modulus
        if residue:
            equations[equation_index][variable_index] = residue
    targets = [
        [int(right_side[equation_index]) % modulus
         for right_side in right_sides]
        for equation_index in range(equation_count)
    ]
    diagnostics = []

    def solve_level(rows, values, current_modulus, depth):
        if time.monotonic() - started > time_limit:
            raise TimeoutError(
                f"sparse module elimination exceeded {time_limit} seconds")
        for row, value in zip(rows, values, strict=True):
            if not row and any(value):
                raise ValueError(
                    f"zero equation has nonzero right side modulo {current_modulus}")
        active = {index for index, row in enumerate(rows) if row}
        nonzero_rows = [set() for _ in range(variable_count)]
        odd_rows = [set() for _ in range(variable_count)]
        for row_index in active:
            for variable_index, coefficient in rows[row_index].items():
                nonzero_rows[variable_index].add(row_index)
                if coefficient & 1:
                    odd_rows[variable_index].add(row_index)
        heap = [
            (len(row_indices), variable_index)
            for variable_index, row_indices in enumerate(odd_rows)
            if row_indices
        ]
        heapq.heapify(heap)
        pivots = []
        initial_nonzeros = sum(len(rows[index]) for index in active)
        active_nonzeros = initial_nonzeros
        peak_nonzeros = initial_nonzeros
        elimination_updates = 0

        while heap:
            degree, pivot_variable = heapq.heappop(heap)
            incident = odd_rows[pivot_variable]
            if not incident or degree != len(incident):
                continue
            pivot_row_index = min(incident, key=lambda index: len(rows[index]))
            pivot_row = rows[pivot_row_index]
            pivot_values = values[pivot_row_index]
            pivot_coefficient = pivot_row[pivot_variable]
            pivot_inverse = pow(pivot_coefficient, -1, current_modulus)

            for row_index in tuple(nonzero_rows[pivot_variable]):
                if row_index == pivot_row_index:
                    continue
                row = rows[row_index]
                old_length = len(row)
                factor = row[pivot_variable] * pivot_inverse % current_modulus
                for variable_index, coefficient in pivot_row.items():
                    old = row.get(variable_index, 0)
                    new = (old - factor * coefficient) % current_modulus
                    if new:
                        row[variable_index] = new
                    elif variable_index in row:
                        del row[variable_index]
                    if bool(old) != bool(new):
                        if new:
                            nonzero_rows[variable_index].add(row_index)
                        else:
                            nonzero_rows[variable_index].discard(row_index)
                    if (old ^ new) & 1:
                        if new & 1:
                            odd_rows[variable_index].add(row_index)
                        else:
                            odd_rows[variable_index].discard(row_index)
                        heapq.heappush(
                            heap,
                            (len(odd_rows[variable_index]), variable_index),
                        )
                values[row_index] = [
                    (value - factor * pivot_value) % current_modulus
                    for value, pivot_value in zip(
                        values[row_index], pivot_values, strict=True)
                ]
                active_nonzeros += len(row) - old_length
                peak_nonzeros = max(peak_nonzeros, active_nonzeros)
                elimination_updates += 1

            active.remove(pivot_row_index)
            active_nonzeros -= len(pivot_row)
            for variable_index, coefficient in pivot_row.items():
                nonzero_rows[variable_index].discard(pivot_row_index)
                if coefficient & 1:
                    odd_rows[variable_index].discard(pivot_row_index)
                    heapq.heappush(
                        heap,
                        (len(odd_rows[variable_index]), variable_index),
                    )
            pivots.append(
                (pivot_variable, pivot_row.copy(), list(pivot_values)))
            if len(pivots) % 256 == 0 and time.monotonic() - started > time_limit:
                raise TimeoutError(
                    f"sparse module elimination exceeded {time_limit} seconds")

        residual_rows = []
        residual_values = []
        for row_index in sorted(active):
            row = rows[row_index]
            value = values[row_index]
            if any(coefficient & 1 for coefficient in row.values()):
                raise AssertionError("unit pivot remained after elimination")
            if any(target & 1 for target in value):
                raise ValueError(
                    f"right side is not in the image modulo {current_modulus}")
            divided_row = {
                variable_index: coefficient // 2
                for variable_index, coefficient in row.items()
                if coefficient
            }
            divided_value = [target // 2 for target in value]
            if divided_row or any(divided_value):
                residual_rows.append(divided_row)
                residual_values.append(divided_value)

        diagnostics.append({
            "depth": depth,
            "modulus": current_modulus,
            "initial_equations": len(rows),
            "initial_nonzeros": initial_nonzeros,
            "unit_pivots": len(pivots),
            "elimination_updates": elimination_updates,
            "residual_equations": len(residual_rows),
            "peak_active_nonzeros": peak_nonzeros,
        })
        if current_modulus == 2:
            if residual_rows:
                raise AssertionError("nonzero row survived division at modulus two")
            solutions = [
                [0] * variable_count for _ in range(right_side_count)]
        else:
            solutions = solve_level(
                residual_rows,
                residual_values,
                current_modulus // 2,
                depth + 1,
            )

        for pivot_variable, pivot_row, pivot_values in reversed(pivots):
            pivot_coefficient = pivot_row[pivot_variable]
            pivot_inverse = pow(pivot_coefficient, -1, current_modulus)
            for right_side_index in range(right_side_count):
                remainder = pivot_values[right_side_index]
                for variable_index, coefficient in pivot_row.items():
                    if variable_index != pivot_variable:
                        remainder -= (
                            coefficient
                            * solutions[right_side_index][variable_index]
                        )
                solutions[right_side_index][pivot_variable] = (
                    pivot_inverse * remainder) % current_modulus
        return solutions

    raw_solutions = solve_level(equations, targets, modulus, 0)
    return (
        [vector(ZZ, solution) for solution in raw_solutions],
        diagnostics,
        time.monotonic() - started,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("compact_export", type=Path)
    parser.add_argument("full_prefix", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--depth", type=int, default=4)
    parser.add_argument("--direct-time-limit", type=float, default=120.0)
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
            try:
                direct_solutions, direct_diagnostics, direct_elapsed = (
                    solve_power_of_two_left(
                        correction_boundary,
                        right_sides,
                        modulus,
                        args.direct_time_limit,
                    )
                )
            except Exception as error:
                records.append({
                    "level": level + 1,
                    "modulus": modulus,
                    "solvable": None,
                    "greedy_hensel_solvable": False,
                    "direct_module_solve_error": (
                        type(error).__name__ + ": " + str(error)),
                })
                break
            solutions = direct_solutions
            if any(
                any(int(value) % modulus for value in (
                    right_sides[basis_index]
                    - solutions[basis_index] * correction_boundary))
                for basis_index in range(len(harmonic_rows))
            ):
                raise AssertionError("invalid direct module solution")
            records.append({
                "level": level + 1,
                "modulus": modulus,
                "solvable": True,
                "greedy_hensel_solvable": False,
                "direct_module_solve": True,
                "direct_module_elapsed_seconds": direct_elapsed,
                "direct_module_diagnostics": direct_diagnostics,
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
