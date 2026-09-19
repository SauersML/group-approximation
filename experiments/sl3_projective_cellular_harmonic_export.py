"""Export an exact integral basis of a certified rational harmonic span.

The full cellular analyzer recomputes every rational boundary rank before it
constructs the harmonic lattice.  At large composite level those ranks may
already be known from independent modular bounds and an exact homology
dimension theorem.  This program performs only the remaining exact kernel
calculation, checks the asserted rank and residual, clears row denominators,
and emits a compact JSON certificate together with the coordinate TSV
consumed by the span-basis-invariant systole screen.  The exported basis need
not be primitive in the ambient integer lattice.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from sage.all import ZZ, lcm, matrix

from sl3_projective_cellular_analyze import build_boundaries, parse


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("harmonic_output", type=Path)
    parser.add_argument("certificate_output", type=Path)
    parser.add_argument("expected_rank", type=int)
    args = parser.parse_args()

    if args.expected_rank <= 0:
        raise ValueError("expected rank must be positive")

    level, degree, orbit_dimensions, cells = parse(args.input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    harmonic_system = boundaries[2].transpose().stack(boundaries[3])
    print("harmonic: computing the rational nullspace", flush=True)
    rational_kernel = harmonic_system.right_kernel_matrix()
    if rational_kernel.nrows() != args.expected_rank:
        raise AssertionError(
            f"rational harmonic rank {rational_kernel.nrows()} differs from "
            f"the certified rank {args.expected_rank}")
    print("harmonic: clearing row denominators", flush=True)
    harmonic_basis = matrix(ZZ, [
        int(lcm(value.denominator() for value in row)) * row
        for row in rational_kernel.rows()
    ])
    harmonic_basis = matrix(ZZ, harmonic_basis, sparse=False).LLL()
    if harmonic_basis.nrows() != args.expected_rank:
        raise AssertionError(
            f"harmonic rank {harmonic_basis.nrows()} differs from "
            f"the certified rank {args.expected_rank}")
    if harmonic_system * harmonic_basis.transpose() != 0:
        raise AssertionError("integral harmonic basis has a nonzero residual")

    digest = hashlib.sha256()
    with args.harmonic_output.open("w", encoding="ascii") as stream:
        header = "coordinate " + " ".join(
            f"basis_{index}" for index in range(harmonic_basis.nrows())) + "\n"
        stream.write(header)
        digest.update(header.encode("ascii"))
        for column in range(harmonic_basis.ncols()):
            line = str(column) + " " + " ".join(
                str(harmonic_basis[row, column])
                for row in range(harmonic_basis.nrows())) + "\n"
            stream.write(line)
            digest.update(line.encode("ascii"))

    gram = harmonic_basis * harmonic_basis.transpose()
    certificate = {
        "level": level,
        "projective_degree": degree,
        "cell_orbit_dimensions": orbit_dimensions,
        "rational_coinvariant_dimensions": dimensions,
        "certified_harmonic_rank": args.expected_rank,
        "harmonic_system_dimensions": [
            int(harmonic_system.nrows()), int(harmonic_system.ncols())],
        "harmonic_basis_sha256": digest.hexdigest(),
        "harmonic_basis_role": (
            "integral basis of the rational harmonic span; primitivity is "
            "not required by the Q-sharp systole algorithm"),
        "harmonic_maximum_absolute_coefficient": max(
            abs(int(value)) for value in harmonic_basis.list()),
        "harmonic_support_sizes": [
            int(sum(1 for value in harmonic_basis.row(row) if value))
            for row in range(harmonic_basis.nrows())],
        "harmonic_gram": [
            [int(value) for value in row] for row in gram.rows()],
        "exact_residual_zero": True,
    }
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    args.certificate_output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
