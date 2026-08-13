"""Construct the dual harmonic carry section from a determinant-one cycle packet.

Let ``K`` be the primitive integral cycle lattice, ``S_sat`` the saturation of
the cellular boundary lattice, and ``Q = P_H(K)``.  If integral cycles
``c_1,...,c_r`` project to a Z-basis of ``Q``, then

    K = S_sat direct_sum <c_1,...,c_r>.

The packet identifies a preferred basis of ``Q^#``.  Pairing that basis with
any primitive basis of ``K`` and applying an integral right inverse gives
ambient integer vectors ``z_i`` which annihilate ``S_sat`` and pair as
``<z_i,c_j> = delta_ij``.  Their orthogonal cycle projections are precisely
the packet-dual basis of ``Q^#``.  Thus the ``z_i`` form an explicit section
of

    0 -> L -> M_Sigma -> Q^# -> 0.

This script certifies every lattice identity exactly.  It also reduces the
section by a fundamental parallelepiped of an explicit sublattice of the
range lattice.  That reduction is an upper bound, not a closest-vector claim.

Run with Sage's Python on MSI, not with a local Python interpreter.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

from sage.all import (
    FreeModule,
    QQ,
    RealField,
    ZZ,
    identity_matrix,
    matrix,
    vector,
)

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_packet_section import read_harmonic_basis


def stage(message: str, start: float) -> float:
    now = time.perf_counter()
    print(f"{message}: {now - start:.3f}s", flush=True)
    return now


def sparse_rows_json(value):
    return [
        [
            {"coordinate": int(column), "coefficient": int(entry)}
            for column, entry in enumerate(value.row(row))
            if entry
        ]
        for row in range(value.nrows())
    ]


def rational_matrix_json(value):
    return [[str(entry) for entry in row] for row in value.rows()]


def read_packet_cycles(path: Path, ambient_dimension: int):
    packet_bytes = path.read_bytes()
    packet = json.loads(packet_bytes)
    selected = packet["shortest_spanning_packet_indices"]
    cycles = []
    for index in selected:
        cycle = vector(ZZ, ambient_dimension)
        for entry in packet["records"][index]["representative"]:
            cycle[entry["coordinate"]] = entry["coefficient"]
        cycles.append(cycle)
    return packet, packet_bytes, matrix(ZZ, cycles)


def section_metric(candidate, qsharp_gram):
    rank = candidate.nrows()
    candidate_gram = candidate * candidate.transpose()
    variable = QQ["t"].gen()
    polynomial = (candidate_gram - variable * qsharp_gram).det()
    polynomial = polynomial / polynomial[rank]
    real_field = RealField(160)
    roots = sorted(
        real_field(root[0]) for root in polynomial.roots(real_field)
    )
    if len(roots) != rank:
        raise AssertionError("generalized section polynomial is not real split")
    return candidate_gram, polynomial, roots


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("packet", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("systole_certificate", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    started = time.perf_counter()
    last = started
    prime, degree, orbit_dimensions, cells = parse(args.cellular_input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    last = stage("parsed cellular complex", last)

    d2 = boundaries[2].change_ring(ZZ)
    d3 = boundaries[3].change_ring(ZZ)
    ambient_dimension = dimensions[2]
    if d3 * d2 != 0:
        raise AssertionError("cellular boundary does not square to zero")

    packet, packet_bytes, cycles = read_packet_cycles(
        args.packet, ambient_dimension)
    harmonic_basis, harmonic_hash = read_harmonic_basis(args.harmonic_basis)
    systole_bytes = args.systole_certificate.read_bytes()
    systole = json.loads(systole_bytes)
    rank = harmonic_basis.nrows()
    if packet["level"] != prime or systole["level"] != prime:
        raise ValueError("level mismatch")
    if harmonic_hash != systole["harmonic_basis_sha256"]:
        raise ValueError("harmonic basis hash mismatch")
    if cycles.nrows() != rank:
        raise ValueError("packet is not square")
    if cycles * d2 != 0:
        raise AssertionError("packet contains a noncycle")

    pairing_basis = matrix(ZZ, systole["pairing_lattice_basis"])
    qsharp_basis = pairing_basis.transpose().inverse() * harmonic_basis
    packet_pairings = qsharp_basis * cycles.transpose()
    if any(entry.denominator() != 1 for entry in packet_pairings.list()):
        raise AssertionError("packet has nonintegral Q-sharp pairings")
    packet_pairings = packet_pairings.change_ring(ZZ)
    if abs(packet_pairings.det()) != 1:
        raise AssertionError("packet does not project to a Z-basis of Q")
    packet_dual_qsharp = packet_pairings.inverse() * qsharp_basis
    if packet_dual_qsharp * cycles.transpose() != identity_matrix(QQ, rank):
        raise AssertionError("packet-dual Q-sharp basis is not dual")
    if d3.change_ring(QQ) * packet_dual_qsharp.transpose() != 0:
        raise AssertionError("packet-dual Q-sharp basis is not harmonic")
    last = stage("recovered packet-dual Q-sharp basis", last)

    print("computing the rational cycle kernel", flush=True)
    rational_cycle_kernel = (
        d2.change_ring(QQ).transpose().right_kernel_matrix())
    print("intersecting the cycle span with the ambient integer lattice",
          flush=True)
    cycle_lattice = rational_cycle_kernel.row_space().intersection(
        FreeModule(ZZ, ambient_dimension))
    cycle_basis = cycle_lattice.basis_matrix()
    cycle_rank = ambient_dimension - d2.rank()
    boundary_rank = cycle_rank - rank
    if cycle_basis.nrows() != cycle_rank:
        raise AssertionError("primitive cycle lattice has the wrong rank")
    if d3.rank() + rank != cycle_rank:
        raise AssertionError("boundary plus harmonic ranks do not fill cycles")
    packet_dual_cycle_pairings = (
        packet_dual_qsharp * cycle_basis.transpose())
    if any(entry.denominator() != 1
           for entry in packet_dual_cycle_pairings.list()):
        raise AssertionError("packet-dual Q-sharp basis has nonintegral pairings")
    packet_dual_cycle_pairings = packet_dual_cycle_pairings.change_ring(ZZ)
    last = stage("constructed primitive cycle lattice", last)

    print("constructing an exact integral right inverse", flush=True)
    cycle_hnf, cycle_transform = cycle_basis.transpose().hermite_form(
        transformation=True, include_zero_rows=True)
    if cycle_hnf[:cycle_rank, :] != identity_matrix(ZZ, cycle_rank):
        raise AssertionError("cycle lattice basis is not primitive")
    if cycle_hnf[cycle_rank:, :] != 0:
        raise AssertionError("cycle column HNF has a nonzero tail")
    right_inverse = cycle_transform.transpose()[:, :cycle_rank]
    if cycle_basis * right_inverse != identity_matrix(ZZ, cycle_rank):
        raise AssertionError("invalid integral right inverse")
    raw_lifts = (
        right_inverse * packet_dual_cycle_pairings.transpose()).transpose()
    if raw_lifts * cycle_basis.transpose() != packet_dual_cycle_pairings:
        raise AssertionError("raw dual lifts have wrong cycle pairings")
    if raw_lifts * cycles.transpose() != identity_matrix(ZZ, rank):
        raise AssertionError("raw dual lifts are not dual to the packet")
    if d3 * raw_lifts.transpose() != 0:
        raise AssertionError("raw dual lifts do not annihilate boundaries")
    last = stage("constructed exact raw dual section", last)

    print("reducing lifts in an explicit range parallelepiped", flush=True)
    range_generators = d2.transpose()
    range_pivots = range_generators.transpose().change_ring(QQ).pivots()
    range_basis = range_generators.matrix_from_rows(range_pivots)
    rational_range = range_basis.change_ring(QQ).row_space()
    reduced = []
    for index, lift in enumerate(raw_lifts.rows()):
        range_component = (
            lift.change_ring(QQ) - packet_dual_qsharp.row(index))
        if range_component not in rational_range:
            raise AssertionError("lift minus Q-sharp vector is not in range")
        coordinates = rational_range.coordinate_vector(range_component)
        integral_coordinates = vector(
            ZZ, [entry.round() for entry in coordinates])
        reduced.append(lift - integral_coordinates * range_basis)
    reduced_lifts = matrix(ZZ, reduced)
    if reduced_lifts * cycle_basis.transpose() != packet_dual_cycle_pairings:
        raise AssertionError("range reduction changed cycle pairings")
    if d3 * reduced_lifts.transpose() != 0:
        raise AssertionError("reduced lifts do not annihilate boundaries")
    last = stage("reduced exact dual section", last)

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
        selected_name = "range_parallelepiped"
    else:
        selected_lifts = raw_lifts
        selected_gram = raw_gram
        selected_polynomial = raw_polynomial
        selected_roots = raw_roots
        selected_name = "cycle_hnf_right_inverse"
    last = stage("computed exact generalized section metrics", last)

    certificate = {
        "level": prime,
        "projective_degree": degree,
        "rational_coinvariant_dimensions": dimensions,
        "cycle_rank": int(cycle_rank),
        "saturated_boundary_rank": int(boundary_rank),
        "harmonic_rank": int(rank),
        "packet_sha256": hashlib.sha256(packet_bytes).hexdigest(),
        "harmonic_basis_sha256": harmonic_hash,
        "systole_certificate_sha256": hashlib.sha256(
            systole_bytes).hexdigest(),
        "qsharp_packet_pairing_matrix": [
            [int(entry) for entry in row]
            for row in packet_pairings.rows()],
        "qsharp_packet_pairing_determinant": int(packet_pairings.det()),
        "packet_complements_saturated_boundary_lattice": True,
        "selected_section": selected_name,
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
        "elapsed_seconds": time.perf_counter() - started,
        "scope": (
            "exact integral section of 0 -> L -> M_Sigma -> Q^# -> 0 "
            "from the determinant-one packet; range-parallelepiped reduction "
            "is a certified upper bound, not a CVP optimum"),
    }
    args.output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(json.dumps({
        "level": prime,
        "cycle_rank": cycle_rank,
        "saturated_boundary_rank": boundary_rank,
        "harmonic_rank": rank,
        "selected_section": selected_name,
        "selected_maximum_section_distortion_squared_approx": str(
            selected_roots[-1]),
        "selected_maximum_section_distortion_approx": str(
            selected_roots[-1].sqrt()),
        "selected_maximum_absolute_coefficient": certificate[
            "selected_maximum_absolute_coefficient"],
        "selected_support_sizes": certificate["selected_support_sizes"],
        "selected_squared_norms": certificate["selected_squared_norms"],
        "elapsed_seconds": certificate["elapsed_seconds"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
