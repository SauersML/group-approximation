"""Certify the two-local correction cokernel and harmonic compatibility.

The sparse local-ring solver records how many unit pivots occur after each
division by two.  Combined with the exact rational rank, these counts recover
the valuations of every nonzero two-local elementary divisor.  This script
also checks that each harmonic demand lies in the rational image and reports
the normalized size of the selected deepest modular lift.

Run with Sage's Python on MSI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

from sage.all import GF, ZZ, matrix

from sl3_projective_harmonic_primary_smt import correction_problem


def harmonic_rows(path: Path) -> list[list[int]]:
    lines = path.read_text(encoding="ascii").splitlines()
    header = lines[0].split()
    if not header or header[0] != "coordinate":
        raise ValueError("invalid harmonic basis header")
    rows = [[] for _ in header[1:]]
    for expected, line in enumerate(lines[1:]):
        fields = line.split()
        if int(fields[0]) != expected or len(fields) != len(rows) + 1:
            raise ValueError("invalid harmonic basis row")
        for basis_index, value in enumerate(fields[1:]):
            rows[basis_index].append(int(value))
    return rows


def centered(value: int, modulus: int) -> int:
    residue = value % modulus
    return residue - modulus if 2 * residue > modulus else residue


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("compact_export", type=Path)
    parser.add_argument("full_prefix", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("depth_certificate", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    basis = harmonic_rows(args.harmonic_basis)
    problems = [
        correction_problem(
            args.compact_export,
            args.full_prefix,
            args.harmonic_basis,
            basis_index,
        )
        for basis_index in range(len(basis))
    ]
    boundary = problems[0]["correction_boundary"]
    if any(problem["correction_boundary"] != boundary for problem in problems[1:]):
        raise AssertionError("harmonic problems have different correction maps")

    rational_rank = int(boundary.rank())
    binary_rank = int(boundary.change_ring(GF(2)).rank())
    augmented_ranks = [
        int(boundary.stack(matrix(ZZ, [problem["right_side"]])).rank())
        for problem in problems
    ]

    certificate_bytes = args.depth_certificate.read_bytes()
    certificate = json.loads(certificate_bytes)
    if certificate["prime"] != problems[0]["prime"]:
        raise AssertionError("depth certificate has the wrong prime")
    if "records" in certificate:
        deepest = certificate["records"][-1]
        if not deepest.get("solvable") or not deepest.get("direct_module_solve"):
            raise ValueError("deepest layer is not a certified direct solve")
        diagnostics = deepest["direct_module_diagnostics"]
        modulus = int(deepest["modulus"])
        centered_correction_squared_norms = (
            deepest["centered_correction_squared_norms"])
        compact_dimension = int(certificate["compact_degree_two_dimension"])
        correction_count = int(certificate["correction_variable_count"])
        certificate_solvable = bool(deepest["solvable"])
    elif certificate.get("selected_basis_congruences_verified"):
        diagnostics = certificate["solver_diagnostics"]
        modulus = int(certificate["modulus"])
        centered_correction_squared_norms = None
        compact_dimension = int(certificate["compact_degree_two_dimension"])
        correction_count = int(certificate["correction_variable_count"])
        certificate_solvable = True
    else:
        raise ValueError("certificate does not contain a verified direct solve")
    pivot_counts = {
        int(record["depth"]): int(record["unit_pivots"])
        for record in diagnostics
        if record["unit_pivots"]
    }
    if sum(pivot_counts.values()) != rational_rank:
        raise AssertionError(
            "local unit pivots do not account for the rational rank")
    if pivot_counts.get(0, 0) != binary_rank:
        raise AssertionError("valuation-zero pivots disagree with binary rank")

    primary_elementary_divisors = {
        str(1 << valuation): multiplicity
        for valuation, multiplicity in pivot_counts.items()
        if valuation > 0
    }
    largest_valuation = max(pivot_counts, default=0)
    if modulus <= 1 << largest_valuation:
        raise AssertionError("certificate is not deeper than the torsion exponent")
    rationally_compatible = [
        rank == rational_rank for rank in augmented_ranks]
    all_depth_two_adic_lifts = [
        compatible and certificate_solvable
        for compatible in rationally_compatible
    ]

    profiles = []
    if centered_correction_squared_norms is not None:
        for basis_index, row in enumerate(basis):
            input_squared = sum(centered(value, modulus) ** 2 for value in row)
            output_squared = int(
                centered_correction_squared_norms[basis_index])
            ratio_squared = Fraction(
                output_squared * compact_dimension,
                correction_count * input_squared,
            )
            profiles.append({
                "basis_index": basis_index,
                "centered_input_squared_norm": input_squared,
                "centered_output_squared_norm": output_squared,
                "normalized_ratio_squared_numerator": ratio_squared.numerator,
                "normalized_ratio_squared_denominator": ratio_squared.denominator,
                "normalized_ratio": math.sqrt(float(ratio_squared)),
            })

    payload = {
        "prime": problems[0]["prime"],
        "projective_degree": problems[0]["degree"],
        "correction_variable_count": boundary.nrows(),
        "equation_count": boundary.ncols(),
        "rational_rank": rational_rank,
        "binary_rank": binary_rank,
        "free_cokernel_rank": boundary.ncols() - rational_rank,
        "two_primary_elementary_divisors": primary_elementary_divisors,
        "augmented_ranks": augmented_ranks,
        "rationally_compatible_harmonic_demands": rationally_compatible,
        "certified_modulus": modulus,
        "all_depth_two_adic_harmonic_lifts": all_depth_two_adic_lifts,
        "selected_section_basis_profiles": profiles,
        "depth_certificate_sha256": hashlib.sha256(
            certificate_bytes).hexdigest(),
    }
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    print("sha256=" + hashlib.sha256(encoded.encode("utf-8")).hexdigest())


if __name__ == "__main__":
    main()
