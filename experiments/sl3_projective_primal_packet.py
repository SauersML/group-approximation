"""Certify a short primal packet basis from an exported Q-sharp Gram matrix.

If ``G`` is the Gram matrix of a basis of ``Q^#``, then ``G^-1`` is the
Gram matrix of the algebraically dual basis of ``(Q^#)^# = Q``.  Clear its
denominators, run exact Gram-LLL, and export the unimodular basis change and
the exactly verified packet norms.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from sage.all import QQ, ZZ, IntegralLattice, lcm, matrix


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    source_bytes = args.input.read_bytes()
    source = json.loads(source_bytes)
    qsharp_gram = matrix(QQ, [
        [QQ(value) for value in row] for row in source["qsharp_gram"]
    ])
    primal_gram = qsharp_gram.inverse()
    scale = lcm(value.denominator() for value in primal_gram.list())
    integral_gram = (scale * primal_gram).change_ring(ZZ)

    reduced_lattice = IntegralLattice(integral_gram).LLL()
    basis_change = reduced_lattice.basis_matrix().change_ring(ZZ)
    if abs(basis_change.det()) != 1:
        raise AssertionError("Gram-LLL basis change is not unimodular")

    reduced_primal_gram = basis_change * primal_gram * basis_change.transpose()
    squared_norms = list(reduced_primal_gram.diagonal())
    threshold = QQ(source["spherical_template_max_squared_norm"])
    maximum = max(squared_norms)

    certificate = {
        "level": source["level"],
        "harmonic_rank": source["harmonic_rank"],
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "primal_gram_denominator_scale": int(scale),
        "primal_packet_basis_change": [
            [int(value) for value in row] for row in basis_change.rows()
        ],
        "primal_packet_squared_norms": [str(value) for value in squared_norms],
        "primal_packet_squared_norms_approx": [
            float(value) for value in squared_norms
        ],
        "primal_packet_maximum_squared_norm": str(maximum),
        "primal_packet_maximum_norm_approx": float(maximum.sqrt()),
        "spherical_template_max_squared_norm": str(threshold),
        "all_packet_norms_below_spherical_threshold": bool(maximum <= threshold),
        "basis_change_determinant": int(basis_change.det()),
        "screen_conclusion": (
            "safe_by_successive_minimum_transference"
            if maximum <= threshold
            else "inconclusive_primal_packet_radius_above_threshold"
        ),
    }
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
