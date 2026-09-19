"""Compute exact boundary and projected-packet indices by sparse HNF.

Let ``B`` be independent cellular boundary rows and ``C`` a rationally full
cycle packet.  With ``S_sat`` the saturated boundary lattice and ``Q`` the
primal harmonic lattice,

    [K : <B,C>] = [S_sat : <B>] [Q : P_H<C>].

Content-normalized unit elimination followed by HNF of the tiny residual
computes the two left-hand lattice indices without constructing ``K`` or a
harmonic basis.  Their quotient is the exact projected packet index in ``Q``.

Run with Sage's Python on MSI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import time
from pathlib import Path

from sage.all import ZZ, matrix

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_dual_section_from_packet import read_packet_cycles
from sl3_projective_dual_section_sparse import solve_unit_system


def index_from_diagnostics(diagnostics):
    index = 1
    hnf_head = None
    for record in diagnostics:
        for divisor, count in record.get(
                "residual_row_gcd_histogram", {}).items():
            divisor = int(divisor)
            if divisor > 1:
                index *= divisor ** int(count)
        if "residual_hnf_head" in record:
            hnf_head = matrix(ZZ, record["residual_hnf_head"])
    if hnf_head is not None:
        index *= abs(int(hnf_head.det()))
    return index


def profile(lattice_rows, time_limit):
    empty_targets = [[] for _ in range(lattice_rows.nrows())]
    solutions, diagnostics, residual, elapsed = solve_unit_system(
        lattice_rows, empty_targets, time_limit, finish_residual_hnf=True)
    if solutions is None or residual:
        raise AssertionError("index profiler left an HNF residual")
    return index_from_diagnostics(diagnostics), diagnostics, elapsed


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("packet", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--time-limit", type=float, default=120.0)
    args = parser.parse_args()

    started = time.monotonic()
    level, degree, orbit_dimensions, cells = parse(args.cellular_input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    d2 = boundaries[2].change_ring(ZZ)
    d3 = boundaries[3].change_ring(ZZ)
    packet, packet_bytes, cycles = read_packet_cycles(
        args.packet, dimensions[2])
    if packet["level"] != level or cycles * d2 != 0:
        raise AssertionError("invalid packet")
    boundary_basis = d3.matrix_from_rows(packet["selected_boundary_rows"])
    if boundary_basis.rank() != d3.rank():
        raise AssertionError("selected boundaries are not rationally full")
    if cycles.nrows() != dimensions[2] - d2.rank() - d3.rank():
        raise AssertionError("packet is not rationally full")

    boundary_index, boundary_diagnostics, boundary_seconds = profile(
        boundary_basis, args.time_limit)
    total_index, total_diagnostics, total_seconds = profile(
        boundary_basis.stack(cycles), args.time_limit)
    if total_index % boundary_index:
        raise AssertionError("boundary index does not divide total index")
    packet_index = total_index // boundary_index
    certificate = {
        "level": level,
        "projective_degree": degree,
        "rational_coinvariant_dimensions": dimensions,
        "boundary_rank": boundary_basis.nrows(),
        "harmonic_rank": cycles.nrows(),
        "packet_sha256": hashlib.sha256(packet_bytes).hexdigest(),
        "selected_boundary_lattice_index_in_saturation": boundary_index,
        "boundary_plus_packet_lattice_index_in_cycles": total_index,
        "projected_packet_index_in_q": packet_index,
        "projected_packet_is_q_basis": packet_index == 1,
        "boundary_index_prime_factors": {
            str(prime): int(exponent)
            for prime, exponent in ZZ(boundary_index).factor()},
        "total_index_prime_factors": {
            str(prime): int(exponent)
            for prime, exponent in ZZ(total_index).factor()},
        "projected_packet_index_prime_factors": {
            str(prime): int(exponent)
            for prime, exponent in ZZ(packet_index).factor()},
        "boundary_elimination_diagnostics": boundary_diagnostics,
        "total_elimination_diagnostics": total_diagnostics,
        "boundary_profile_seconds": boundary_seconds,
        "total_profile_seconds": total_seconds,
        "elapsed_seconds": time.monotonic() - started,
        "scope": (
            "exact lattice indices from content factors and residual column "
            "HNF; projected packet index uses the exact multiplicative index "
            "formula [K:<B,C>]=[S_sat:<B>][Q:P_H<C>]"),
    }
    args.output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(json.dumps({
        "level": level,
        "selected_boundary_lattice_index_in_saturation": boundary_index,
        "boundary_plus_packet_lattice_index_in_cycles": total_index,
        "projected_packet_index_in_q": packet_index,
        "projected_packet_is_q_basis": packet_index == 1,
        "elapsed_seconds": certificate["elapsed_seconds"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
