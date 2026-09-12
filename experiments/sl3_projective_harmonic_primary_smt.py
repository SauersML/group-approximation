"""Export and exactly verify harmonic carry equations as bit-vector SMT.

For ``m=2^k``, the congruence ``x A = b (mod m)`` is literally a system of
width-``k`` bit-vector equations.  The exporter constructs the same correction
matrix and harmonic right sides as the primary-coupling and MILP audits, then
writes a ``QF_BV`` instance for one harmonic basis vector.  A model produced by
an external SMT solver is accepted only after multiplication by the original
Sage integer matrix verifies every congruence exactly.

Typical use on MSI (export), followed by a machine with ``z3`` (solve), and MSI
again (verify)::

    sage -python sl3_projective_harmonic_primary_smt.py ... instance.smt2 \
        --basis-index 0 --modulus 8
    z3 -T:600 instance.smt2 > model.txt
    sage -python sl3_projective_harmonic_primary_smt.py ... unused.smt2 \
        --basis-index 0 --modulus 8 --model model.txt --witness witness.tsv
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

from sage.all import ZZ, vector

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_derived_e1 import coordinate_indices, read_boundary
from sl3_projective_harmonic_primary_coupling import (
    compact_representatives,
    read_harmonic_basis,
    signed_torsion_representatives,
)


VALUE_PATTERN = re.compile(r"\(x(\d+)\s+#b([01]+)\)")


def centered(value: int, modulus: int) -> int:
    residue = value % modulus
    return residue - modulus if 2 * residue > modulus else residue


def bv_literal(value: int, width: int, modulus: int) -> str:
    return "#b" + format(value % modulus, f"0{width}b")


def correction_problem(compact_export, full_prefix, harmonic_basis, basis_index):
    prime, degree, orbit_dimensions, cells = parse(compact_export)
    compact_dimensions, _compact_boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    representatives = compact_representatives(degree, cells)
    full_boundary = read_boundary(Path(str(full_prefix) + "-d2.tsv"), ZZ)

    cell_generators = (8, 9)
    two_cell_torsion_points = [
        signed_torsion_representatives(degree, cells[(2, cell_index)])
        for cell_index in (1, 2)
    ]
    correction_indices = [
        cell_generators[cell_index - 1] * degree + point
        for cell_index in (1, 2)
        for point in two_cell_torsion_points[cell_index - 1]
    ] + coordinate_indices(2, 1, degree) + coordinate_indices(2, 0, degree)
    correction_boundary = full_boundary.matrix_from_rows(correction_indices)

    harmonic_rows = read_harmonic_basis(
        harmonic_basis, compact_dimensions[2])
    if not 0 <= basis_index < len(harmonic_rows):
        raise ValueError("basis index is out of range")
    compact_lift = vector(ZZ, full_boundary.nrows())
    for compact_coordinate, coefficient in enumerate(
            harmonic_rows[basis_index]):
        if coefficient == 0:
            continue
        cell_index, point, source_sign = representatives[compact_coordinate]
        generator = cell_generators[cell_index - 1]
        compact_lift[generator * degree + point] += source_sign * coefficient
    right_side = -(compact_lift * full_boundary)
    return {
        "prime": prime,
        "degree": degree,
        "torsion_orbit_counts": list(map(len, two_cell_torsion_points)),
        "correction_boundary": correction_boundary,
        "right_side": right_side,
    }


def export_smt(path: Path, boundary, right_side, modulus: int) -> dict:
    width = modulus.bit_length() - 1
    by_equation = [[] for _ in range(boundary.ncols())]
    for (variable_index, equation_index), coefficient in boundary.dict().items():
        coefficient = int(coefficient) % modulus
        if coefficient:
            by_equation[equation_index].append((variable_index, coefficient))

    with path.open("w", encoding="utf-8") as output:
        output.write("(set-logic QF_BV)\n")
        output.write("(set-option :produce-models true)\n")
        for variable_index in range(boundary.nrows()):
            output.write(
                f"(declare-fun x{variable_index} () (_ BitVec {width}))\n")
        for equation_index, terms in enumerate(by_equation):
            rhs = bv_literal(int(right_side[equation_index]), width, modulus)
            if not terms:
                if int(right_side[equation_index]) % modulus:
                    output.write("(assert false)\n")
                continue
            expressions = []
            for variable_index, coefficient in terms:
                variable = f"x{variable_index}"
                if coefficient == 1:
                    expressions.append(variable)
                elif coefficient == modulus - 1:
                    expressions.append(f"(bvneg {variable})")
                else:
                    literal = bv_literal(coefficient, width, modulus)
                    expressions.append(f"(bvmul {literal} {variable})")
            expression = expressions[0]
            for term in expressions[1:]:
                expression = f"(bvadd {expression} {term})"
            output.write(f"(assert (= {expression} {rhs}))\n")
        output.write("(check-sat)\n")
        variables = " ".join(
            f"x{variable_index}" for variable_index in range(boundary.nrows()))
        output.write(f"(get-value ({variables}))\n")

    return {
        "variable_count": boundary.nrows(),
        "equation_count": boundary.ncols(),
        "matrix_nonzeros": len(boundary.dict()),
        "smt_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def verify_model(model_path: Path, boundary, right_side, modulus: int,
                 witness_path: Path | None) -> dict:
    text = model_path.read_text(encoding="utf-8")
    status = next((line.strip() for line in text.splitlines() if line.strip()), "")
    if status != "sat":
        return {"solver_status": status, "exact_congruence_verified": False}
    values = {
        int(index): int(bits, 2)
        for index, bits in VALUE_PATTERN.findall(text)
    }
    if len(values) != boundary.nrows():
        raise ValueError(
            f"model contains {len(values)} of {boundary.nrows()} variables")
    correction = vector(
        ZZ, [values[index] for index in range(boundary.nrows())])
    residual = correction * boundary - right_side
    verified = all(int(value) % modulus == 0 for value in residual)
    if not verified:
        raise AssertionError("SMT model failed exact integer verification")

    if witness_path is not None:
        lines = [f"{boundary.nrows()} {modulus}\n"]
        lines.extend(
            f"{index} {int(value)}\n"
            for index, value in enumerate(correction) if value
        )
        witness_path.write_text("".join(lines), encoding="utf-8")
    centered_values = [centered(int(value), modulus) for value in correction]
    return {
        "solver_status": status,
        "exact_congruence_verified": True,
        "correction_support": len(correction.support()),
        "centered_correction_squared_norm": sum(
            value * value for value in centered_values),
        "centered_maximum_absolute_coefficient": max(
            map(abs, centered_values)),
        "witness_sha256": (
            hashlib.sha256(witness_path.read_bytes()).hexdigest()
            if witness_path is not None else None
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("compact_export", type=Path)
    parser.add_argument("full_prefix", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("smt_output", type=Path)
    parser.add_argument("--basis-index", type=int, required=True)
    parser.add_argument("--modulus", type=int, default=8)
    parser.add_argument("--model", type=Path)
    parser.add_argument("--witness", type=Path)
    args = parser.parse_args()
    if args.modulus < 2 or args.modulus & (args.modulus - 1):
        raise ValueError("modulus must be a positive power of two")

    problem = correction_problem(
        args.compact_export, args.full_prefix, args.harmonic_basis,
        args.basis_index)
    boundary = problem.pop("correction_boundary")
    right_side = problem.pop("right_side")
    payload = {
        "prime": problem["prime"],
        "projective_degree": problem["degree"],
        "basis_index": args.basis_index,
        "modulus": args.modulus,
        "two_cell_orientation_torsion_orbits": problem["torsion_orbit_counts"],
    }
    if args.model is None:
        payload.update(export_smt(
            args.smt_output, boundary, right_side, args.modulus))
    else:
        payload.update(verify_model(
            args.model, boundary, right_side, args.modulus, args.witness))
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
