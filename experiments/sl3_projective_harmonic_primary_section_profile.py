"""Exhaust the selected modular section on a rank-two harmonic plane.

The sparse local-ring solver returns one deterministic correction for each
integral harmonic basis vector.  Linearity modulo ``2^k`` gives a selected
section on their full modular span.  This script exhausts that span, verifies
every congruence exactly, and computes exact worst-case squared norm ratios.

These are norms of the *selected* section, hence certified upper bounds for
minimum-norm lifting.  They are not CVP minima.

Run with Sage's Python on MSI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
from sage.all import ZZ, vector

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_derived_e1 import coordinate_indices, read_boundary
from sl3_projective_harmonic_primary_coupling import (
    compact_representatives,
    read_harmonic_basis,
    signed_torsion_representatives,
)
from sl3_projective_harmonic_primary_hensel import (
    solve_power_of_two_left,
)


def centered_array(values: np.ndarray, modulus: int) -> np.ndarray:
    residues = np.remainder(values, modulus)
    return np.where(2 * residues > modulus, residues - modulus, residues)


def ratio_record(
    numerator_squared: int,
    numerator_dimension: int,
    denominator_squared: int,
    denominator_dimension: int,
) -> tuple[Fraction, float]:
    squared = Fraction(
        numerator_squared * denominator_dimension,
        numerator_dimension * denominator_squared,
    )
    return squared, math.sqrt(float(squared))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("compact_export", type=Path)
    parser.add_argument("full_prefix", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--depth", type=int, default=6)
    parser.add_argument("--time-limit", type=float, default=180.0)
    args = parser.parse_args()
    if args.depth < 1:
        raise ValueError("depth must be positive")
    modulus = 1 << args.depth

    prime, degree, orbit_dimensions, cells = parse(args.compact_export)
    compact_dimensions, _compact_boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    compact_dimension = compact_dimensions[2]
    representatives = compact_representatives(degree, cells)
    harmonic_rows = read_harmonic_basis(
        args.harmonic_basis, compact_dimension)
    if len(harmonic_rows) != 2:
        raise ValueError("the exhaustive profiler currently expects rank two")

    full_boundary = read_boundary(
        Path(str(args.full_prefix) + "-d2.tsv"), ZZ)
    cell_generators = (8, 9)
    torsion_points = [
        signed_torsion_representatives(degree, cells[(2, cell_index)])
        for cell_index in (1, 2)
    ]
    correction_indices = [
        cell_generators[cell_index - 1] * degree + point
        for cell_index in (1, 2)
        for point in torsion_points[cell_index - 1]
    ] + coordinate_indices(2, 1, degree) + coordinate_indices(2, 0, degree)
    correction_boundary = full_boundary.matrix_from_rows(correction_indices)

    compact_indices = [
        cell_generators[cell_index - 1] * degree + point
        for cell_index, point, _source_sign in representatives
    ]
    overlap = set(compact_indices).intersection(correction_indices)
    if overlap:
        raise AssertionError(
            "canonical compact lift overlaps the correction coordinates")

    right_sides = []
    for integer_row in harmonic_rows:
        compact_lift = [0] * full_boundary.nrows()
        for compact_coordinate, coefficient in enumerate(integer_row):
            if coefficient:
                cell_index, point, source_sign = representatives[compact_coordinate]
                generator = cell_generators[cell_index - 1]
                compact_lift[generator * degree + point] += (
                    source_sign * coefficient)
        right_sides.append(-vector(ZZ, compact_lift) * full_boundary)

    solutions, diagnostics, _elapsed = solve_power_of_two_left(
        correction_boundary, right_sides, modulus, args.time_limit)
    for basis_index, solution in enumerate(solutions):
        residual = solution * correction_boundary - right_sides[basis_index]
        if any(int(value) % modulus for value in residual):
            raise AssertionError("selected basis correction is invalid")

    harmonic = np.asarray(
        [[int(value) % modulus for value in row] for row in harmonic_rows],
        dtype=np.int64,
    )
    corrections = np.asarray(
        [[int(value) for value in solution] for solution in solutions],
        dtype=np.int64,
    )
    correction_count = correction_boundary.nrows()
    full_dimension = full_boundary.nrows()

    maximum_correction = None
    maximum_full = None
    zero_input_combinations = []
    correction_ratios = []
    full_ratios = []
    checked = 0
    for first in range(modulus):
        for second in range(modulus):
            if first == 0 and second == 0:
                continue
            coefficients = np.asarray([first, second], dtype=np.int64)
            compact_vector = centered_array(coefficients @ harmonic, modulus)
            input_squared = int(compact_vector @ compact_vector)
            if input_squared == 0:
                zero_input_combinations.append([first, second])
                continue
            correction_vector = centered_array(
                coefficients @ corrections, modulus)
            correction_squared = int(correction_vector @ correction_vector)
            full_squared = input_squared + correction_squared

            correction_ratio, correction_approx = ratio_record(
                correction_squared,
                correction_count,
                input_squared,
                compact_dimension,
            )
            full_ratio, full_approx = ratio_record(
                full_squared,
                full_dimension,
                input_squared,
                compact_dimension,
            )
            correction_ratios.append(correction_approx)
            full_ratios.append(full_approx)
            candidate = {
                "coefficients_modulus": [first, second],
                "centered_input_squared_norm": input_squared,
                "centered_correction_squared_norm": correction_squared,
                "centered_full_lift_squared_norm": full_squared,
            }
            if (maximum_correction is None
                    or correction_ratio > maximum_correction[0]):
                maximum_correction = (correction_ratio, candidate.copy())
            if maximum_full is None or full_ratio > maximum_full[0]:
                maximum_full = (full_ratio, candidate.copy())
            checked += 1

    if zero_input_combinations:
        raise AssertionError(
            "harmonic basis is dependent modulo the selected modulus")

    def finish_maximum(item, numerator_dimension, full: bool):
        squared, record = item
        record = dict(record)
        record.update({
            "normalized_ratio_squared_numerator": squared.numerator,
            "normalized_ratio_squared_denominator": squared.denominator,
            "normalized_ratio": math.sqrt(float(squared)),
            "numerator_dimension": numerator_dimension,
            "denominator_dimension": compact_dimension,
            "includes_compact_lift": full,
        })
        return record

    def quantiles(values):
        data = np.asarray(values, dtype=np.float64)
        return {
            "minimum": float(np.min(data)),
            "median": float(np.quantile(data, 0.5)),
            "q90": float(np.quantile(data, 0.9)),
            "q99": float(np.quantile(data, 0.99)),
            "maximum": float(np.max(data)),
        }

    payload = {
        "prime": prime,
        "projective_degree": degree,
        "modulus": modulus,
        "harmonic_rank": len(harmonic_rows),
        "nonzero_combinations_checked": checked,
        "compact_degree_two_dimension": compact_dimension,
        "correction_variable_count": correction_count,
        "full_degree_two_dimension": full_dimension,
        "canonical_compact_correction_overlap": len(overlap),
        "selected_basis_congruences_verified": True,
        "solver_diagnostics": diagnostics,
        "maximum_normalized_correction_ratio": finish_maximum(
            maximum_correction, correction_count, False),
        "maximum_normalized_full_lift_ratio": finish_maximum(
            maximum_full, full_dimension, True),
        "correction_ratio_distribution": quantiles(correction_ratios),
        "full_lift_ratio_distribution": quantiles(full_ratios),
        "scope": (
            "Exhaustive norm of one deterministic modular section; this is "
            "an upper bound for minimum-norm lifting, not a CVP optimum."
        ),
    }
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    print("sha256=" + hashlib.sha256(encoded.encode("utf-8")).hexdigest())


if __name__ == "__main__":
    main()
