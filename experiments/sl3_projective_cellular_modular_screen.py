"""Quick modular rank screen for an exported projective cellular complex.

The signed coinvariant boundary matrices are integral.  Reducing them modulo
several auxiliary primes gives certified lower bounds on their rational ranks,
and hence upper bounds on rational homology dimensions.  Matching an
independent rational lower bound can determine the rational dimension before
the slower exact kernel and lattice computation finishes.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from sage.all import GF, is_prime

from sl3_projective_cellular_analyze import build_boundaries, parse


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--fields", default="101,1009,10007")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    characteristics = [int(value) for value in args.fields.split(",")]
    if not characteristics or any(not is_prime(value) for value in characteristics):
        parser.error("--fields must be a nonempty comma-separated list of primes")

    level, degree, orbit_dimensions, cells = parse(args.input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    results = []
    for characteristic in characteristics:
        field = GF(characteristic)
        reduced = {
            degree_index: boundary.change_ring(field)
            for degree_index, boundary in boundaries.items()
        }
        square_zero = {
            str(degree_index): bool(
                (reduced[degree_index] * reduced[degree_index - 1]).is_zero())
            for degree_index in range(2, len(orbit_dimensions))
        }
        if not all(square_zero.values()):
            raise AssertionError("a modular boundary product is nonzero")
        ranks = {
            str(degree_index): int(boundary.rank())
            for degree_index, boundary in reduced.items()
        }
        homology = {
            str(degree_index): int(
                dimensions[degree_index]
                - ranks.get(str(degree_index), 0)
                - ranks.get(str(degree_index + 1), 0))
            for degree_index in range(len(orbit_dimensions))
        }
        results.append({
            "characteristic": characteristic,
            "boundary_ranks": ranks,
            "homology_dimensions": homology,
            "boundary_squared_zero": square_zero,
        })

    certificate = {
        "level": level,
        "projective_degree": degree,
        "cell_orbit_dimensions": orbit_dimensions,
        "rational_coinvariant_dimensions": dimensions,
        "fields": results,
    }
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
