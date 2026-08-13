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
    lift_data = source.get("harmonic_lift_sequence") or {}
    raw_qsharp_gram = source.get("qsharp_gram") or lift_data.get("qsharp_gram")
    rank = source.get("harmonic_rank")
    if rank is None:
        rank = source.get("integral_harmonic_rank", 0)
    level = source.get("level", source.get("prime"))
    threshold = QQ(source["spherical_template_max_squared_norm"])

    if not raw_qsharp_gram:
        if rank != 0:
            raise ValueError("positive harmonic rank without a Q-sharp Gram matrix")
        certificate = {
            "level": level,
            "harmonic_rank": 0,
            "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
            "spherical_template_max_squared_norm": str(threshold),
            "screen_conclusion": "safe_zero_harmonic_rank",
        }
        rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
        args.output.write_text(rendered, encoding="utf-8")
        print(rendered, end="")
        return

    qsharp_gram = matrix(QQ, [
        [QQ(value) for value in row] for row in raw_qsharp_gram
    ])
    if qsharp_gram.nrows() != rank:
        raise AssertionError("Q-sharp Gram rank does not match harmonic rank")
    primal_gram = qsharp_gram.inverse()
    scale = lcm(value.denominator() for value in primal_gram.list())
    integral_gram = (scale * primal_gram).change_ring(ZZ)

    reduced_lattice = IntegralLattice(integral_gram).LLL()
    basis_change = reduced_lattice.basis_matrix().change_ring(ZZ)
    if abs(basis_change.det()) != 1:
        raise AssertionError("Gram-LLL basis change is not unimodular")

    reduced_primal_gram = basis_change * primal_gram * basis_change.transpose()
    squared_norms = list(reduced_primal_gram.diagonal())
    maximum = max(squared_norms)
    absolute_row_sums = [
        sum(abs(value) for value in row)
        for row in reduced_primal_gram.rows()
    ]
    maximum_row_sum = max(absolute_row_sums)

    certificate = {
        "level": level,
        "harmonic_rank": rank,
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "primal_gram_denominator_scale": int(scale),
        "primal_packet_basis_change": [
            [int(value) for value in row] for row in basis_change.rows()
        ],
        "primal_packet_squared_norms": [str(value) for value in squared_norms],
        "primal_packet_squared_norms_approx": [
            float(value) for value in squared_norms
        ],
        "primal_packet_gram": [
            [str(value) for value in row]
            for row in reduced_primal_gram.rows()
        ],
        "primal_packet_gram_approx": [
            [float(value) for value in row]
            for row in reduced_primal_gram.rows()
        ],
        "primal_packet_absolute_gram_row_sums": [
            str(value) for value in absolute_row_sums
        ],
        "primal_packet_absolute_gram_row_sums_approx": [
            float(value) for value in absolute_row_sums
        ],
        "primal_packet_maximum_squared_norm": str(maximum),
        "primal_packet_maximum_squared_norm_approx": float(maximum),
        "primal_packet_maximum_norm_approx": float(maximum.sqrt()),
        "primal_packet_maximum_absolute_gram_row_sum": str(maximum_row_sum),
        "primal_packet_maximum_absolute_gram_row_sum_approx": float(
            maximum_row_sum),
        "spherical_template_max_squared_norm": str(threshold),
        "all_packet_norms_below_spherical_threshold": bool(maximum <= threshold),
        "gram_operator_below_spherical_threshold_by_row_sum": bool(
            maximum_row_sum <= threshold),
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
