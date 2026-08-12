"""Screen a projective cellular cycle kernel for short fundamental circuits.

This is a finite-field discriminator, not an integral certificate.  The
right-kernel echelon basis records the fundamental dependencies selected by
the sparse modular elimination.  Small balanced coefficients and bounded
row supports are evidence for the exact certificate in
``TRUE_FUNDAMENTAL_CIRCUIT_PACKET_CERTIFICATE.md``; dense rows or large
balanced coefficients only show that this particular pivot choice fails.

Run with Sage's Python on MSI, not with a local Python interpreter.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from sage.all import GF

from sl3_projective_cellular_analyze import build_boundaries, parse


def quantiles(values: list[int]) -> dict[str, int]:
    ordered = sorted(values)
    if not ordered:
        return {"minimum": 0, "median": 0, "p90": 0, "p99": 0, "maximum": 0}

    def select(numerator: int, denominator: int) -> int:
        index = ((len(ordered) - 1) * numerator) // denominator
        return int(ordered[index])

    return {
        "minimum": int(ordered[0]),
        "median": select(1, 2),
        "p90": select(9, 10),
        "p99": select(99, 100),
        "maximum": int(ordered[-1]),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--characteristic", type=int, default=1009)
    parser.add_argument("--expected-rank", type=int)
    args = parser.parse_args()

    field = GF(args.characteristic)
    level, degree, orbit_dimensions, cells = parse(args.input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)

    cycle_matrix = boundaries[2].transpose().change_ring(field)
    print(
        f"level={level} matrix={cycle_matrix.nrows()}x{cycle_matrix.ncols()} "
        f"characteristic={args.characteristic}",
        flush=True,
    )
    kernel = cycle_matrix.right_kernel_matrix()
    rank = cycle_matrix.ncols() - kernel.nrows()
    if args.expected_rank is not None and rank != args.expected_rank:
        raise AssertionError(
            f"modular rank {rank} differs from expected rank {args.expected_rank}")
    if cycle_matrix * kernel.transpose() != 0:
        raise AssertionError("kernel basis has a nonzero residual")

    support_sizes = []
    balanced_l1 = []
    balanced_l2_squared = []
    balanced_maximum = []
    coefficients = 0
    coefficients_of_size_one = 0
    for row in kernel.rows():
        balanced = []
        for value in row:
            integer = int(value)
            if integer == 0:
                continue
            representative = min(integer, args.characteristic - integer)
            balanced.append(representative)
        support_sizes.append(len(balanced))
        balanced_l1.append(sum(balanced))
        balanced_l2_squared.append(sum(value * value for value in balanced))
        balanced_maximum.append(max(balanced, default=0))
        coefficients += len(balanced)
        coefficients_of_size_one += sum(value == 1 for value in balanced)

    certificate = {
        "level": int(level),
        "projective_degree": int(degree),
        "cell_orbit_dimensions": orbit_dimensions,
        "rational_coinvariant_dimensions": dimensions,
        "characteristic": int(args.characteristic),
        "cycle_matrix_dimensions": [
            int(cycle_matrix.nrows()), int(cycle_matrix.ncols())],
        "cycle_matrix_rank": int(rank),
        "kernel_dimension": int(kernel.nrows()),
        "kernel_residual_zero": True,
        "basis_role": (
            "finite-field right-kernel echelon basis; a pivot-choice screen, "
            "not an integral fundamental-circuit certificate"),
        "support_size": quantiles(support_sizes),
        "balanced_l1": quantiles(balanced_l1),
        "balanced_l2_squared": quantiles(balanced_l2_squared),
        "balanced_maximum_coefficient": quantiles(balanced_maximum),
        "nonzero_coefficient_count": int(coefficients),
        "balanced_unit_coefficient_count": int(coefficients_of_size_one),
        "balanced_unit_coefficient_fraction": (
            coefficients_of_size_one / coefficients if coefficients else 1.0),
    }
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
