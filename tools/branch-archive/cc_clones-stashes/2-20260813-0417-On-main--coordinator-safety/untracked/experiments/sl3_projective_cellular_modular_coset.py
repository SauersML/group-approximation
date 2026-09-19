"""Compute modular coset-leader lower bounds for a cellular lift class.

Let ``L`` be the saturated integral range lattice.  For every prime modulus,
the orthogonal cycle code is a parity-check code for ``L/pL``.  An integral
lift has squared Euclidean norm at least the sum of the squared centered
residues of its reduction modulo ``p``.  This Sage program minimizes that
finite modular cost with GLPK and exports an exact syndrome verification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from sage.all import GF, MixedIntegerLinearProgram, QQ, ZZ, vector

from sl3_projective_cellular_analyze import build_boundaries, parse


def centered_residue(value: int, modulus: int) -> int:
    residue = value % modulus
    if 2 * residue > modulus:
        residue -= modulus
    return residue


def certify_no_ternary_cost_below_four(check, syndrome):
    """Exhaust all signed supports of size at most three over F_3."""

    if check.base_ring().order() != 3:
        return None
    target = tuple(int(value) for value in syndrome)
    zero = (0,) * check.nrows()
    if target == zero:
        raise AssertionError("zero support realizes the ternary syndrome")
    columns = [tuple(int(check[row, column])
                     for row in range(check.nrows()))
               for column in range(check.ncols())]
    atoms = {}
    for column, value in enumerate(columns):
        for sign in (1, -1):
            signed = tuple((sign * entry) % 3 for entry in value)
            atoms.setdefault(signed, []).append((column, sign))
    if target in atoms:
        raise AssertionError("one coordinate realizes the ternary syndrome")

    pair_cases = 0
    for left in range(check.ncols()):
        for right in range(left + 1, check.ncols()):
            for left_sign in (1, -1):
                for right_sign in (1, -1):
                    pair_cases += 1
                    pair = tuple((left_sign * columns[left][row]
                                  + right_sign * columns[right][row]) % 3
                                 for row in range(check.nrows()))
                    if pair == target:
                        raise AssertionError(
                            "two coordinates realize the ternary syndrome")
                    remainder = tuple((target[row] - pair[row]) % 3
                                      for row in range(check.nrows()))
                    for third, _ in atoms.get(remainder, ()):
                        if third not in (left, right):
                            raise AssertionError(
                                "three coordinates realize the ternary syndrome")
    return {
        "method": "exhaustive signed-column meet-in-the-middle",
        "signed_pair_cases_checked": pair_cases,
        "excluded_centered_residue_costs": [0, 1, 2, 3],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("lift", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--modulus", type=int, required=True)
    parser.add_argument("--exact-lift-output", type=Path)
    args = parser.parse_args()
    modulus = args.modulus
    if modulus < 2 or not ZZ(modulus).is_prime():
        raise ValueError("modulus must be prime")

    prime, degree, orbit_dimensions, cells = parse(args.input)
    dimensions, boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    d2_integer = boundaries[2].change_ring(ZZ)
    cycle_basis = d2_integer.transpose().right_kernel_matrix()
    check_modular = cycle_basis.change_ring(GF(modulus))
    if check_modular.rank() != cycle_basis.nrows():
        raise AssertionError("cycle checks lost rank modulo the selected prime")

    lift_rows = args.lift.read_text().splitlines()
    if lift_rows[0] != "coordinate qsharp lift":
        raise ValueError("unexpected lift header")
    qsharp = vector(QQ, [line.split()[1] for line in lift_rows[1:]])
    lift = vector(ZZ, [int(line.split()[2]) for line in lift_rows[1:]])
    if len(lift) != dimensions[2]:
        raise ValueError("lift has the wrong ambient dimension")
    syndrome_integer = cycle_basis * lift
    syndrome = check_modular * lift.change_ring(GF(modulus))

    residues = list(range(-(modulus // 2), modulus // 2 + 1))
    residues.remove(0)
    problem = MixedIntegerLinearProgram(maximization=False, solver="GLPK")
    selected = problem.new_variable(binary=True, nonnegative=True)
    quotients = problem.new_variable(integer=True, nonnegative=False)
    coordinate_expressions = []
    objective = 0
    for column in range(dimensions[2]):
        problem.add_constraint(problem.sum(
            selected[column, residue] for residue in residues) <= 1)
        expression = problem.sum(
            residue * selected[column, residue] for residue in residues)
        coordinate_expressions.append(expression)
        objective += problem.sum(
            residue * residue * selected[column, residue]
            for residue in residues)
    problem.set_objective(objective)

    for row in range(cycle_basis.nrows()):
        coefficients = [centered_residue(
            int(cycle_basis[row, column]), modulus)
                        for column in range(dimensions[2])]
        syndrome_value = centered_residue(
            int(syndrome_integer[row]), modulus)
        expression = problem.sum(
            coefficients[column] * coordinate_expressions[column]
            for column in range(dimensions[2]) if coefficients[column])
        absolute_bound = sum(abs(value) for value in coefficients) * (
            modulus // 2)
        quotient_bound = (absolute_bound + abs(syndrome_value)) // modulus + 1
        problem.set_min(quotients[row], -quotient_bound)
        problem.set_max(quotients[row], quotient_bound)
        problem.add_constraint(
            expression - modulus * quotients[row] == syndrome_value)

    candidate_cost = sum(centered_residue(
        int(value), modulus) ** 2 for value in lift)
    problem.add_constraint(objective <= candidate_cost)
    optimum = int(round(problem.solve(log=2)))

    solution_values = problem.get_values(selected)
    solution = vector(ZZ, dimensions[2])
    solution_entries = []
    for (column, residue), value in solution_values.items():
        if value <= 0.5:
            continue
        solution[column] = residue
        solution_entries.append([int(column), int(residue)])
    solution_cost = sum(int(value) ** 2 for value in solution)
    if solution_cost != optimum:
        raise AssertionError("modular solution cost differs from optimum")
    if check_modular * solution.change_ring(GF(modulus)) != syndrome:
        raise AssertionError("modular solution has the wrong syndrome")
    ternary_lower_certificate = certify_no_ternary_cost_below_four(
        check_modular, syndrome)

    exact_cocycle = (boundaries[3].change_ring(ZZ)
                      * solution.column()).is_zero()
    exact_pairings = cycle_basis * solution == syndrome_integer
    exact_lift_hash = None
    if exact_cocycle and exact_pairings and args.exact_lift_output:
        digest = hashlib.sha256()
        with args.exact_lift_output.open("w", encoding="ascii") as stream:
            header = "coordinate qsharp lift\n"
            stream.write(header)
            digest.update(header.encode("ascii"))
            for coordinate, (qsharp_value, lift_value) in enumerate(
                    zip(qsharp, solution)):
                line = f"{coordinate} {qsharp_value} {lift_value}\n"
                stream.write(line)
                digest.update(line.encode("ascii"))
        exact_lift_hash = digest.hexdigest()

    result = {
        "prime": prime,
        "modulus": modulus,
        "ambient_dimension": dimensions[2],
        "range_rank": int(d2_integer.rank()),
        "parity_check_rank": int(check_modular.rank()),
        "candidate_centered_residue_cost": candidate_cost,
        "modular_coset_leader_squared_cost": optimum,
        "modular_coset_leader_entries": solution_entries,
        "syndrome_support": [row for row, value in enumerate(syndrome) if value],
        "solver": "GLPK branch-and-bound",
        "verification": "modular_check_times_solution_equals_syndrome",
        "solution_is_exact_integral_lift": bool(
            exact_cocycle and exact_pairings),
        "exact_cocycle_residual_zero": bool(exact_cocycle),
        "exact_cycle_pairings_match": bool(exact_pairings),
        "exact_lift_squared_norm": (
            optimum if exact_cocycle and exact_pairings else None),
        "exact_lift_sha256": exact_lift_hash,
        "ternary_lower_certificate": ternary_lower_certificate,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
