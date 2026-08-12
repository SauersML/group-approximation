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

from fpylll import CVP, IntegerMatrix, LLL
from sage.all import QQ, RealField, ZZ, identity_matrix, matrix

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_dual_section_from_packet import (
    read_packet_cycles,
    sparse_rows_json,
)
from sl3_projective_dual_section_sparse import (
    greedy_row_lattice_reduce,
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


def to_fpylll(basis):
    result = IntegerMatrix(basis.nrows(), basis.ncols())
    for row in range(basis.nrows()):
        for column in range(basis.ncols()):
            result[row, column] = int(basis[row, column])
    return result


def saturated_babai_reduce(lifts, d2):
    """Reduce packet-dual lifts in the full integral annihilator.

    The raw row lattice of ``d2.transpose()`` need not be primitive.  Its
    saturation is the integral orthogonal complement of the integral cycle
    lattice.  Computing the two kernels below constructs that saturation
    directly, including every torsion direction at once.
    """
    cycle_basis = d2.transpose().right_kernel_matrix()
    saturated_basis = cycle_basis.right_kernel_matrix()
    if saturated_basis * cycle_basis.transpose() != 0:
        raise AssertionError("saturated annihilator does not kill cycles")
    if saturated_basis.nrows() + cycle_basis.nrows() != d2.ncols():
        raise AssertionError("cycle and annihilator ranks do not complement")

    reduced_basis = to_fpylll(saturated_basis)
    LLL.reduction(reduced_basis, delta=0.99)
    reduced_rows = []
    for lift in lifts.rows():
        correction = CVP.babai(
            reduced_basis, tuple(-int(entry) for entry in lift), delta=0.99)
        candidate = lift + matrix(ZZ, 1, len(correction), correction).row(0)
        reduced_rows.append(candidate)
    reduced_lifts = matrix(ZZ, reduced_rows)
    return reduced_lifts, {
        "cycle_lattice_rank": cycle_basis.nrows(),
        "saturated_annihilator_rank": saturated_basis.nrows(),
        "saturated_annihilator_basis_maximum_absolute_coefficient": max(
            abs(int(entry)) for entry in saturated_basis.list()),
        "reduction": "exact double-kernel saturation plus fpylll LLL/Babai",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("packet", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--time-limit", type=float, default=120.0)
    parser.add_argument("--greedy-sweeps", type=int, default=20)
    parser.add_argument("--finish-residual-hnf", action="store_true")
    parser.add_argument("--lll-saturated-reduce", action="store_true")
    parser.add_argument(
        "--saturation-direction-certificate",
        action="append",
        default=[],
        type=Path,
    )
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

    reduction_generators = d2.transpose()
    saturation_certificate_hashes = []
    for certificate_path in args.saturation_direction_certificate:
        certificate_bytes = certificate_path.read_bytes()
        certificate = json.loads(certificate_bytes)
        if certificate["level"] != level:
            raise ValueError("saturation direction level mismatch")
        if certificate["boundary_degree"] != 2:
            raise ValueError("saturation direction has the wrong degree")
        direction = matrix(ZZ, 1, ambient_dimension, {
            (0, entry["coordinate"]): entry["coefficient"]
            for entry in certificate["saturation_direction"]
        })
        selected_rows = reduction_generators.matrix_from_rows(
            certificate["selected_bad_field_row_indices"]
            + [certificate["extra_rational_row_index"]])
        dependence = matrix(
            ZZ, 1, selected_rows.nrows(),
            certificate["lifted_dependence_coefficients"])
        if dependence * selected_rows != certificate["prime"] * direction:
            raise AssertionError("saturation direction certificate is invalid")
        reduction_generators = reduction_generators.stack(direction)
        saturation_certificate_hashes.append(
            hashlib.sha256(certificate_bytes).hexdigest())

    reduced_lifts, reduction_changes = greedy_row_lattice_reduce(
        raw_lifts, reduction_generators, args.greedy_sweeps)
    if d3 * reduced_lifts.transpose() != 0:
        raise AssertionError("range reduction changed boundary annihilation")
    if cycles * reduced_lifts.transpose() != identity_matrix(ZZ, rank):
        raise AssertionError("range reduction changed packet pairings")

    saturated_lifts = None
    saturated_diagnostics = None
    if args.lll_saturated_reduce:
        saturated_lifts, saturated_diagnostics = saturated_babai_reduce(
            reduced_lifts, d2)
        if d3 * saturated_lifts.transpose() != 0:
            raise AssertionError(
                "saturated reduction changed boundary annihilation")
        if cycles * saturated_lifts.transpose() != identity_matrix(ZZ, rank):
            raise AssertionError("saturated reduction changed packet pairings")

    packet_gram, packet_polynomial, packet_roots = synthesis_metric(cycles)
    raw_gram, raw_polynomial, raw_roots = synthesis_metric(raw_lifts)
    reduced_gram, reduced_polynomial, reduced_roots = synthesis_metric(
        reduced_lifts)
    candidates = [
        (raw_roots[-1], raw_lifts, raw_gram, raw_polynomial, raw_roots,
         "raw_unit_elimination"),
        (reduced_roots[-1], reduced_lifts, reduced_gram, reduced_polynomial,
         reduced_roots,
         "greedy_certified_saturation_reduced"
         if saturation_certificate_hashes
         else "greedy_raw_coboundary_reduced"),
    ]
    saturated_gram = None
    if saturated_lifts is not None:
        saturated_gram, saturated_polynomial, saturated_roots = synthesis_metric(
            saturated_lifts)
        candidates.append((
            saturated_roots[-1], saturated_lifts, saturated_gram,
            saturated_polynomial, saturated_roots,
            "full_saturated_lll_babai"))
    (_selected_metric, selected_lifts, selected_gram, selected_polynomial,
     selected_roots, selected_name) = min(candidates, key=lambda item: item[0])
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
        "greedy_row_lattice_reduction_changes_by_sweep": (
            reduction_changes),
        "saturation_direction_certificate_sha256": (
            saturation_certificate_hashes),
        "reduction_generator_count": reduction_generators.nrows(),
        "full_saturated_reduction_diagnostics": saturated_diagnostics,
        "packet_ambient_gram": [
            [int(entry) for entry in row] for row in packet_gram.rows()],
        "packet_ambient_synthesis_polynomial_monic": str(packet_polynomial),
        "packet_ambient_synthesis_roots_approx": [
            str(root) for root in packet_roots],
        "raw_lift_gram": [
            [int(entry) for entry in row] for row in raw_gram.rows()],
        "reduced_lift_gram": [
            [int(entry) for entry in row] for row in reduced_gram.rows()],
        "full_saturated_lift_gram": (
            None if saturated_gram is None else
            [[int(entry) for entry in row] for row in saturated_gram.rows()]),
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
        "full_saturated_lifts": (
            None if saturated_lifts is None else
            sparse_rows_json(saturated_lifts)),
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
            "the Riesz norm is a basis-free upper bound; when requested, "
            "double-kernel reduction constructs the full saturated "
            "annihilator exactly and applies LLL/Babai, but is not a CVP "
            "optimum"),
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
