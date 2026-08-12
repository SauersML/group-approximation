"""Certify the torsion subgroup of cellular first homology.

For free chains ``C_2 -> C_1 -> C_0``, the saturation quotient

    Sat(im d_2) / im d_2

is the torsion subgroup of ``coker(d_2)``, hence also of ``H_1`` because
``im(d_1)`` is free.  The exact index profiler computes its order.  For each
prime divisor, the rank drop modulo that prime is the minimum number of
generators of the corresponding primary part.  If every drop is one, the
torsion group is cyclic.  Run with Sage on MSI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

from sage.all import GF, ZZ

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_packet_index_sparse import profile


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--time-limit", type=float, default=120.0)
    args = parser.parse_args()

    started = time.monotonic()
    input_bytes = args.cellular_input.read_bytes()
    level, degree, orbit_dimensions, cells = parse(args.cellular_input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    d2 = boundaries[2].change_ring(ZZ)
    row_matrix = d2.transpose()
    rational_rank = d2.rank()
    torsion_order, diagnostics, profile_seconds = profile(
        row_matrix, args.time_limit)
    factorization = ZZ(torsion_order).factor()
    primary_parts = []
    cyclic = True
    for prime, exponent in factorization:
        modular_rank = d2.change_ring(GF(prime)).rank()
        generator_count = rational_rank - modular_rank
        cyclic = cyclic and generator_count == 1
        primary_parts.append({
            "prime": int(prime),
            "order_exponent": int(exponent),
            "modular_rank": int(modular_rank),
            "minimum_generator_count": int(generator_count),
            "cyclic_primary_part": generator_count == 1,
        })

    certificate = {
        "level": level,
        "projective_degree": degree,
        "rational_coinvariant_dimensions": dimensions,
        "d2_dimensions": list(d2.dimensions()),
        "d2_rational_rank": int(rational_rank),
        "h1_torsion_order": int(torsion_order),
        "h1_torsion_order_prime_factors": {
            str(prime): int(exponent) for prime, exponent in factorization},
        "primary_parts": primary_parts,
        "h1_torsion_is_cyclic": bool(cyclic),
        "h1_torsion_invariant_factors": (
            [int(torsion_order)] if cyclic and torsion_order > 1 else []),
        "exact_index_diagnostics": diagnostics,
        "profile_seconds": profile_seconds,
        "elapsed_seconds": time.monotonic() - started,
        "cellular_input_sha256": hashlib.sha256(input_bytes).hexdigest(),
        "proof": (
            "Sat(im d2)/im d2 is Tor(coker d2)=Tor(H1); its order is "
            "the exact row-lattice saturation index. For each prime, the "
            "rational-to-modular rank drop is the primary generator count."),
    }
    args.output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(json.dumps({
        "level": level,
        "d2_rational_rank": int(rational_rank),
        "h1_torsion_order": int(torsion_order),
        "h1_torsion_order_prime_factors": certificate[
            "h1_torsion_order_prime_factors"],
        "primary_parts": primary_parts,
        "h1_torsion_is_cyclic": bool(cyclic),
        "h1_torsion_invariant_factors": certificate[
            "h1_torsion_invariant_factors"],
        "elapsed_seconds": certificate["elapsed_seconds"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
