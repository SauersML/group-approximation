"""Solve packet-dual harmonic carry fibers by sparse integer unit elimination.

The determinant-one packet gives an integral cycle decomposition

    K = S_sat direct_sum <c_1,...,c_r>.

Hence a lift of the packet-dual vector ``u_i`` is exactly an ambient integer
row ``z_i`` satisfying

    <z_i, boundary_j> = 0,    <z_i, c_j> = delta_ij.

This script solves those seven right-hand sides directly.  It deliberately
avoids constructing the full primitive cycle lattice and its enormous HNF
transformation.  Sparse elimination uses only coefficients ``+1`` and ``-1``
as pivots, so every operation is integral and exact.  If unit elimination is
not complete, the script exports the exact non-unit residual rather than
starting a generic long-running normal-form computation.

Run with Sage's Python on MSI, not with a local Python interpreter.
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
import json
import math
import time
from pathlib import Path

from sage.all import QQ, RealField, ZZ, identity_matrix, matrix, vector

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_dual_section_from_packet import (
    rational_matrix_json,
    read_packet_cycles,
    section_metric,
    sparse_rows_json,
)
from sl3_projective_packet_section import read_harmonic_basis


def solve_unit_system(coefficient_matrix, targets, time_limit):
    """Solve ``coefficient_matrix * x = targets`` over Z by unit pivots.

    Rows whose coefficients have a common divisor are divided by it when the
    same divisor divides every target.  This preserves the exact integral
    solution set.  A residual primitive row without a unit coefficient is
    returned as an explicit obstruction to this fast method.
    """
    started = time.monotonic()
    equation_count = coefficient_matrix.nrows()
    variable_count = coefficient_matrix.ncols()
    target_count = len(targets[0]) if targets else 0
    rows = [dict() for _ in range(equation_count)]
    for (row, column), coefficient in coefficient_matrix.dict().items():
        value = int(coefficient)
        if value:
            rows[row][column] = value
    values = [list(row) for row in targets]
    active = {row for row in range(equation_count) if rows[row]}
    for row in range(equation_count):
        if not rows[row] and any(values[row]):
            raise ValueError("zero equation has nonzero target")

    pivots = []
    diagnostics = []
    total_pivots = 0
    round_index = 0

    while active:
        if time.monotonic() - started > time_limit:
            raise TimeoutError(
                f"integer unit elimination exceeded {time_limit} seconds")
        nonzero_rows = [set() for _ in range(variable_count)]
        unit_rows = [set() for _ in range(variable_count)]
        for row_index in active:
            for variable_index, coefficient in rows[row_index].items():
                nonzero_rows[variable_index].add(row_index)
                if abs(coefficient) == 1:
                    unit_rows[variable_index].add(row_index)
        heap = [
            (len(incidence), variable)
            for variable, incidence in enumerate(unit_rows) if incidence
        ]
        heapq.heapify(heap)
        initial_nonzeros = sum(len(rows[row]) for row in active)
        active_nonzeros = initial_nonzeros
        peak_nonzeros = initial_nonzeros
        elimination_updates = 0
        round_pivots = 0

        while heap:
            degree, pivot_variable = heapq.heappop(heap)
            incident_units = unit_rows[pivot_variable]
            if not incident_units or degree != len(incident_units):
                continue
            pivot_row_index = min(
                incident_units, key=lambda row: len(rows[row]))
            pivot_row = rows[pivot_row_index]
            pivot_values = values[pivot_row_index]
            pivot_coefficient = pivot_row[pivot_variable]
            if abs(pivot_coefficient) != 1:
                raise AssertionError("selected pivot is not an integer unit")

            for row_index in tuple(nonzero_rows[pivot_variable]):
                if row_index == pivot_row_index:
                    continue
                row = rows[row_index]
                old_length = len(row)
                factor = row[pivot_variable] * pivot_coefficient
                for variable_index, coefficient in pivot_row.items():
                    old = row.get(variable_index, 0)
                    new = old - factor * coefficient
                    if new:
                        row[variable_index] = new
                    elif variable_index in row:
                        del row[variable_index]
                    if bool(old) != bool(new):
                        if new:
                            nonzero_rows[variable_index].add(row_index)
                        else:
                            nonzero_rows[variable_index].discard(row_index)
                    if (abs(old) == 1) != (abs(new) == 1):
                        if abs(new) == 1:
                            unit_rows[variable_index].add(row_index)
                        else:
                            unit_rows[variable_index].discard(row_index)
                        heapq.heappush(
                            heap,
                            (len(unit_rows[variable_index]), variable_index),
                        )
                values[row_index] = [
                    value - factor * pivot_value
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
                if abs(coefficient) == 1:
                    unit_rows[variable_index].discard(pivot_row_index)
                    heapq.heappush(
                        heap,
                        (len(unit_rows[variable_index]), variable_index),
                    )
            pivots.append(
                (pivot_variable, pivot_row.copy(), list(pivot_values)))
            total_pivots += 1
            round_pivots += 1
            if total_pivots % 128 == 0:
                if time.monotonic() - started > time_limit:
                    raise TimeoutError(
                        "integer unit elimination exceeded time limit")

        zero_rows = []
        for row_index in active:
            if not rows[row_index]:
                if any(values[row_index]):
                    raise ValueError("elimination produced 0 = nonzero")
                zero_rows.append(row_index)
        active.difference_update(zero_rows)

        divided_rows = 0
        gcd_histogram = {}
        for row_index in sorted(active):
            divisor = 0
            for coefficient in rows[row_index].values():
                divisor = math.gcd(divisor, abs(coefficient))
            gcd_histogram[str(divisor)] = gcd_histogram.get(str(divisor), 0) + 1
            if divisor <= 1:
                continue
            if any(value % divisor for value in values[row_index]):
                raise ValueError(
                    "row content does not divide the target; no integral solution")
            rows[row_index] = {
                variable: coefficient // divisor
                for variable, coefficient in rows[row_index].items()
            }
            values[row_index] = [
                value // divisor for value in values[row_index]]
            divided_rows += 1

        diagnostics.append({
            "round": round_index,
            "initial_active_equations": (
                len(active) + round_pivots + len(zero_rows)),
            "initial_nonzeros": initial_nonzeros,
            "unit_pivots": round_pivots,
            "elimination_updates": elimination_updates,
            "peak_active_nonzeros": peak_nonzeros,
            "residual_equations": len(active),
            "divided_residual_rows": divided_rows,
            "residual_row_gcd_histogram": gcd_histogram,
        })
        if not active:
            break
        if divided_rows == 0:
            break
        round_index += 1

    elapsed = time.monotonic() - started
    if active:
        residual_rows = []
        for row_index in sorted(active):
            row = rows[row_index]
            residual_rows.append({
                "row": row_index,
                "support_size": len(row),
                "maximum_absolute_coefficient": max(
                    abs(value) for value in row.values()),
                "coefficient_gcd": math.gcd(
                    *[abs(value) for value in row.values()]),
                "target": values[row_index],
                "entries": [
                    {"variable": variable, "coefficient": coefficient}
                    for variable, coefficient in sorted(row.items())
                ],
            })
        return None, diagnostics, residual_rows, elapsed

    solutions = [[0] * variable_count for _ in range(target_count)]
    for pivot_variable, pivot_row, pivot_values in reversed(pivots):
        pivot_coefficient = pivot_row[pivot_variable]
        for target_index in range(target_count):
            remainder = pivot_values[target_index]
            for variable_index, coefficient in pivot_row.items():
                if variable_index != pivot_variable:
                    remainder -= (
                        coefficient * solutions[target_index][variable_index])
            solutions[target_index][pivot_variable] = (
                pivot_coefficient * remainder)
    return (
        [vector(ZZ, solution) for solution in solutions],
        diagnostics,
        [],
        elapsed,
    )


def greedy_range_reduce(lifts, range_generators, sweeps):
    reduced = [vector(ZZ, lift) for lift in lifts.rows()]
    generators = []
    for row in range(range_generators.nrows()):
        generator = range_generators.row(row)
        norm_squared = generator.dot_product(generator)
        if norm_squared:
            generators.append((generator, norm_squared))
    changes_by_sweep = []
    for _sweep in range(sweeps):
        changes = 0
        for lift_index, lift in enumerate(reduced):
            for generator, norm_squared in generators:
                inner = lift.dot_product(generator)
                multiple = ZZ((QQ(inner) / norm_squared).round())
                if not multiple:
                    continue
                norm_change = (
                    -2 * multiple * inner
                    + multiple * multiple * norm_squared)
                if norm_change < 0:
                    lift = lift - multiple * generator
                    changes += 1
            reduced[lift_index] = lift
        changes_by_sweep.append(changes)
        if not changes:
            break
    return matrix(ZZ, reduced), changes_by_sweep


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("packet", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("systole_certificate", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--time-limit", type=float, default=120.0)
    parser.add_argument("--greedy-sweeps", type=int, default=3)
    args = parser.parse_args()

    started = time.monotonic()
    level, degree, orbit_dimensions, cells = parse(args.cellular_input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    d2 = boundaries[2].change_ring(ZZ)
    d3 = boundaries[3].change_ring(ZZ)
    ambient_dimension = dimensions[2]

    packet, packet_bytes, cycles = read_packet_cycles(
        args.packet, ambient_dimension)
    harmonic_basis, harmonic_hash = read_harmonic_basis(args.harmonic_basis)
    systole_bytes = args.systole_certificate.read_bytes()
    systole = json.loads(systole_bytes)
    rank = harmonic_basis.nrows()
    if packet["level"] != level or systole["level"] != level:
        raise ValueError("level mismatch")
    if harmonic_hash != systole["harmonic_basis_sha256"]:
        raise ValueError("harmonic basis hash mismatch")
    if cycles.nrows() != rank or cycles * d2 != 0:
        raise AssertionError("packet is not a square packet of cycles")

    selected_boundary_rows = packet["selected_boundary_rows"]
    boundary_basis = d3.matrix_from_rows(selected_boundary_rows)
    equation_matrix = boundary_basis.stack(cycles)
    targets = [[0] * rank for _ in range(equation_matrix.nrows())]
    for index in range(rank):
        targets[boundary_basis.nrows() + index][index] = 1

    print(
        f"level={level} equations={equation_matrix.nrows()} "
        f"variables={equation_matrix.ncols()} targets={rank}", flush=True)
    solutions, diagnostics, residual_rows, solve_seconds = solve_unit_system(
        equation_matrix, targets, args.time_limit)

    common = {
        "level": level,
        "projective_degree": degree,
        "rational_coinvariant_dimensions": dimensions,
        "equation_count": equation_matrix.nrows(),
        "variable_count": equation_matrix.ncols(),
        "target_count": rank,
        "selected_boundary_row_count": boundary_basis.nrows(),
        "packet_sha256": hashlib.sha256(packet_bytes).hexdigest(),
        "harmonic_basis_sha256": harmonic_hash,
        "systole_certificate_sha256": hashlib.sha256(
            systole_bytes).hexdigest(),
        "unit_elimination_diagnostics": diagnostics,
        "unit_elimination_seconds": solve_seconds,
    }
    if solutions is None:
        certificate = {
            **common,
            "complete_integral_section": False,
            "residual_equation_count": len(residual_rows),
            "residual_nonzeros": sum(
                row["support_size"] for row in residual_rows),
            "residual_maximum_absolute_coefficient": max(
                row["maximum_absolute_coefficient"]
                for row in residual_rows),
            "residual_rows": residual_rows,
            "elapsed_seconds": time.monotonic() - started,
            "scope": (
                "exact non-unit residual after exhaustive sparse integer "
                "unit elimination; no generic normal-form fallback was run"),
        }
        args.output.write_text(
            json.dumps(certificate, indent=2, sort_keys=True) + "\n",
            encoding="utf-8")
        print(json.dumps({
            "complete_integral_section": False,
            "residual_equation_count": len(residual_rows),
            "residual_nonzeros": certificate["residual_nonzeros"],
            "residual_maximum_absolute_coefficient": certificate[
                "residual_maximum_absolute_coefficient"],
            "unit_elimination_seconds": solve_seconds,
        }, indent=2, sort_keys=True))
        return

    raw_lifts = matrix(ZZ, solutions)
    target_matrix = matrix(ZZ, targets)
    if equation_matrix * raw_lifts.transpose() != target_matrix:
        raise AssertionError("sparse solver returned an invalid solution")
    if d3 * raw_lifts.transpose() != 0:
        raise AssertionError("selected boundary rows did not imply all boundaries")
    if cycles * raw_lifts.transpose() != identity_matrix(ZZ, rank):
        raise AssertionError("lifts are not packet-dual")

    reduced_lifts, reduction_changes = greedy_range_reduce(
        raw_lifts, d2.transpose(), args.greedy_sweeps)
    if d3 * reduced_lifts.transpose() != 0:
        raise AssertionError("range reduction changed boundary annihilation")
    if cycles * reduced_lifts.transpose() != identity_matrix(ZZ, rank):
        raise AssertionError("range reduction changed packet pairings")

    pairing_basis = matrix(ZZ, systole["pairing_lattice_basis"])
    qsharp_basis = pairing_basis.transpose().inverse() * harmonic_basis
    packet_pairings = qsharp_basis * cycles.transpose()
    if any(entry.denominator() != 1 for entry in packet_pairings.list()):
        raise AssertionError("packet pairings are not integral")
    packet_pairings = packet_pairings.change_ring(ZZ)
    if abs(packet_pairings.det()) != 1:
        raise AssertionError("packet does not project to a Z-basis of Q")
    packet_dual_qsharp = packet_pairings.inverse() * qsharp_basis
    qsharp_gram = packet_dual_qsharp * packet_dual_qsharp.transpose()
    raw_gram, raw_polynomial, raw_roots = section_metric(
        raw_lifts, qsharp_gram)
    reduced_gram, reduced_polynomial, reduced_roots = section_metric(
        reduced_lifts, qsharp_gram)
    if reduced_roots[-1] <= raw_roots[-1]:
        selected_lifts = reduced_lifts
        selected_gram = reduced_gram
        selected_polynomial = reduced_polynomial
        selected_roots = reduced_roots
        selected_name = "greedy_range_reduced"
    else:
        selected_lifts = raw_lifts
        selected_gram = raw_gram
        selected_polynomial = raw_polynomial
        selected_roots = raw_roots
        selected_name = "raw_unit_elimination"

    certificate = {
        **common,
        "complete_integral_section": True,
        "residual_equation_count": 0,
        "greedy_range_reduction_changes_by_sweep": reduction_changes,
        "qsharp_packet_pairing_matrix": [
            [int(entry) for entry in row] for row in packet_pairings.rows()],
        "qsharp_packet_pairing_determinant": int(packet_pairings.det()),
        "packet_dual_qsharp_gram": rational_matrix_json(qsharp_gram),
        "raw_lift_gram": [
            [int(entry) for entry in row] for row in raw_gram.rows()],
        "reduced_lift_gram": [
            [int(entry) for entry in row] for row in reduced_gram.rows()],
        "selected_lift_gram": [
            [int(entry) for entry in row] for row in selected_gram.rows()],
        "raw_section_polynomial_monic": str(raw_polynomial),
        "reduced_section_polynomial_monic": str(reduced_polynomial),
        "selected_section_polynomial_monic": str(selected_polynomial),
        "raw_section_roots_approx": [str(root) for root in raw_roots],
        "reduced_section_roots_approx": [str(root) for root in reduced_roots],
        "selected_section_roots_approx": [str(root) for root in selected_roots],
        "selected_section": selected_name,
        "selected_maximum_section_distortion_squared_approx": str(
            selected_roots[-1]),
        "selected_maximum_section_distortion_approx": str(
            selected_roots[-1].sqrt()),
        "raw_lifts": sparse_rows_json(raw_lifts),
        "reduced_lifts": sparse_rows_json(reduced_lifts),
        "selected_maximum_absolute_coefficient": max(
            abs(int(entry)) for entry in selected_lifts.list()),
        "selected_support_sizes": [
            sum(1 for entry in selected_lifts.row(row) if entry)
            for row in range(rank)],
        "selected_squared_norms": [
            int(selected_gram[row, row]) for row in range(rank)],
        "elapsed_seconds": time.monotonic() - started,
        "scope": (
            "exact integral section of the packet-dual harmonic lift "
            "sequence; greedy range reduction is an upper bound, not CVP"),
    }
    args.output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(json.dumps({
        "complete_integral_section": True,
        "selected_section": selected_name,
        "selected_maximum_section_distortion_squared_approx": str(
            selected_roots[-1]),
        "selected_maximum_section_distortion_approx": str(
            selected_roots[-1].sqrt()),
        "selected_maximum_absolute_coefficient": certificate[
            "selected_maximum_absolute_coefficient"],
        "selected_support_sizes": certificate["selected_support_sizes"],
        "selected_squared_norms": certificate["selected_squared_norms"],
        "unit_elimination_seconds": solve_seconds,
        "elapsed_seconds": certificate["elapsed_seconds"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
