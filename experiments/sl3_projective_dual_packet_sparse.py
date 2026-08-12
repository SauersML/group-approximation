"""Certify a packet as an integral harmonic basis via ambient dual lifts.

This is the packet-only companion to
``sl3_projective_dual_section_sparse.py``.  It does not require an exported
harmonic basis or a precomputed ``Q^#`` lattice.  If all packet-coordinate
functionals extend to ambient integer rows annihilating every boundary, then
the projected packet is automatically a Z-basis of ``Q``.

The script also gives a basis-free Riesz upper bound for the resulting dual
section.  If ``C`` is the ambient packet matrix and ``Z`` the lift matrix,
then

    ||s|| <= ||C||_op ||Z||_op.

This follows from the packet-section theorem because harmonic projection can
only decrease the primal synthesis norm.

Run with Sage's Python on MSI, not with a local Python interpreter.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

from sage.all import QQ, RealField, ZZ, identity_matrix, matrix

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_dual_section_from_packet import (
    read_packet_cycles,
    sparse_rows_json,
)
from sl3_projective_dual_section_sparse import (
    greedy_range_reduce,
    solve_unit_system,
)


def synthesis_metric(candidate):
    rank = candidate.nrows()
    gram = candidate * candidate.transpose()
    variable = QQ["t"].gen()
    polynomial = (gram - variable * identity_matrix(QQ, rank)).det()
    polynomial = polynomial / polynomial[rank]
    real_field = RealField(160)
    roots = sorted(
        real_field(root[0]) for root in polynomial.roots(real_field)
    )
    if len(roots) != rank:
        raise AssertionError("Gram characteristic polynomial is not real split")
    return gram, polynomial, roots


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("packet", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--time-limit", type=float, default=120.0)
    parser.add_argument("--greedy-sweeps", type=int, default=20)
    parser.add_argument("--finish-residual-hnf", action="store_true")
    args = parser.parse_args()

    started = time.monotonic()
    level, degree, orbit_dimensions, cells = parse(args.cellular_input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    d2 = boundaries[2].change_ring(ZZ)
    d3 = boundaries[3].change_ring(ZZ)
    ambient_dimension = dimensions[2]
    packet, packet_bytes, cycles = read_packet_cycles(
        args.packet, ambient_dimension)
    rank = cycles.nrows()
    if packet["level"] != level:
        raise ValueError("level mismatch")
    if cycles * d2 != 0:
        raise AssertionError("packet contains a noncycle")
    if rank != ambient_dimension - d2.rank() - d3.rank():
        raise AssertionError("packet size differs from rational H_2 rank")

    selected_boundary_rows = packet["selected_boundary_rows"]
    boundary_basis = d3.matrix_from_rows(selected_boundary_rows)
    if boundary_basis.rank() != d3.rank():
        raise AssertionError("selected boundary rows do not span boundaries")
    equation_matrix = boundary_basis.stack(cycles)
    targets = [[0] * rank for _ in range(equation_matrix.nrows())]
    for index in range(rank):
        targets[boundary_basis.nrows() + index][index] = 1

    print(
        f"level={level} equations={equation_matrix.nrows()} "
        f"variables={equation_matrix.ncols()} targets={rank}", flush=True)
    solutions, diagnostics, residual_rows, solve_seconds = solve_unit_system(
        equation_matrix, targets, args.time_limit, args.finish_residual_hnf)
    common = {
        "level": level,
        "projective_degree": degree,
        "rational_coinvariant_dimensions": dimensions,
        "rational_harmonic_rank": rank,
        "equation_count": equation_matrix.nrows(),
        "variable_count": equation_matrix.ncols(),
        "target_count": rank,
        "selected_boundary_row_count": boundary_basis.nrows(),
        "packet_sha256": hashlib.sha256(packet_bytes).hexdigest(),
        "unit_elimination_diagnostics": diagnostics,
        "unit_elimination_seconds": solve_seconds,
    }
    if solutions is None:
        certificate = {
            **common,
            "complete_integral_section": False,
            "projected_packet_is_q_basis": False,
            "residual_equation_count": len(residual_rows),
            "residual_nonzeros": sum(
                row["support_size"] for row in residual_rows),
            "residual_rows": residual_rows,
            "elapsed_seconds": time.monotonic() - started,
            "scope": (
                "exact non-unit residual after sparse integer elimination; "
                "failure of this selected solver is not a nonexistence proof"),
        }
        args.output.write_text(
            json.dumps(certificate, indent=2, sort_keys=True) + "\n",
            encoding="utf-8")
        print(json.dumps({
            "complete_integral_section": False,
            "residual_equation_count": len(residual_rows),
            "residual_nonzeros": certificate["residual_nonzeros"],
            "unit_elimination_seconds": solve_seconds,
        }, indent=2, sort_keys=True))
        return

    raw_lifts = matrix(ZZ, solutions)
    target_matrix = matrix(ZZ, targets)
    if equation_matrix * raw_lifts.transpose() != target_matrix:
        raise AssertionError("sparse solver returned an invalid solution")
    if d3 * raw_lifts.transpose() != 0:
        raise AssertionError("lifts do not annihilate every boundary")
    if cycles * raw_lifts.transpose() != identity_matrix(ZZ, rank):
        raise AssertionError("lifts are not packet-dual")

    reduced_lifts, reduction_changes = greedy_range_reduce(
        raw_lifts, d2.transpose(), args.greedy_sweeps)
    if d3 * reduced_lifts.transpose() != 0:
        raise AssertionError("range reduction changed boundary annihilation")
    if cycles * reduced_lifts.transpose() != identity_matrix(ZZ, rank):
        raise AssertionError("range reduction changed packet pairings")

    packet_gram, packet_polynomial, packet_roots = synthesis_metric(cycles)
    raw_gram, raw_polynomial, raw_roots = synthesis_metric(raw_lifts)
    reduced_gram, reduced_polynomial, reduced_roots = synthesis_metric(
        reduced_lifts)
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
    real_field = RealField(160)
    riesz_bound_squared = packet_roots[-1] * selected_roots[-1]
    riesz_bound = real_field(riesz_bound_squared).sqrt()

    certificate = {
        **common,
        "complete_integral_section": True,
        "projected_packet_is_q_basis": True,
        "proof_of_q_basis": (
            "the packet-coordinate dual basis extends to ambient integer "
            "functionals annihilating every boundary; hence it lies in Q^#"),
        "residual_equation_count": 0,
        "greedy_range_reduction_changes_by_sweep": reduction_changes,
        "packet_ambient_gram": [
            [int(entry) for entry in row] for row in packet_gram.rows()],
        "packet_ambient_synthesis_polynomial_monic": str(packet_polynomial),
        "packet_ambient_synthesis_roots_approx": [
            str(root) for root in packet_roots],
        "raw_lift_gram": [
            [int(entry) for entry in row] for row in raw_gram.rows()],
        "reduced_lift_gram": [
            [int(entry) for entry in row] for row in reduced_gram.rows()],
        "selected_lift_gram": [
            [int(entry) for entry in row] for row in selected_gram.rows()],
        "raw_lift_synthesis_polynomial_monic": str(raw_polynomial),
        "reduced_lift_synthesis_polynomial_monic": str(reduced_polynomial),
        "selected_lift_synthesis_polynomial_monic": str(selected_polynomial),
        "selected_lift_synthesis_roots_approx": [
            str(root) for root in selected_roots],
        "selected_section": selected_name,
        "packet_riesz_section_bound_squared_approx": str(
            riesz_bound_squared),
        "packet_riesz_section_bound_approx": str(riesz_bound),
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
            "exact integral Q-basis and packet-dual section certificate; "
            "the Riesz norm is a basis-free upper bound and greedy range "
            "reduction is not a CVP optimum"),
    }
    args.output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(json.dumps({
        "complete_integral_section": True,
        "projected_packet_is_q_basis": True,
        "packet_riesz_section_bound_approx": str(riesz_bound),
        "selected_maximum_absolute_coefficient": certificate[
            "selected_maximum_absolute_coefficient"],
        "selected_support_sizes": certificate["selected_support_sizes"],
        "selected_squared_norms": certificate["selected_squared_norms"],
        "unit_elimination_seconds": solve_seconds,
        "elapsed_seconds": certificate["elapsed_seconds"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
