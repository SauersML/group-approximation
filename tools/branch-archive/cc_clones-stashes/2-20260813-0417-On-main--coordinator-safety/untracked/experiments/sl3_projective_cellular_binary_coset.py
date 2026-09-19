"""Compute the binary coset-leader lower bound for a cellular lift class.

If ``L`` is the saturated integral range lattice, then reduction modulo two
identifies ``L/2L`` with the row space of the cellular boundary.  The
orthogonal cycle code is therefore a parity-check code for lift classes.
The Hamming weight of the corresponding binary coset is a rigorous lower
bound for the squared Euclidean norm of every integral lift.

This Sage program solves that finite syndrome-decoding problem with GLPK and
exports the resulting support together with exact syndrome verification.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from sage.all import GF, MixedIntegerLinearProgram, ZZ, vector

from sl3_projective_cellular_analyze import build_boundaries, parse


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("lift", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    prime, degree, orbit_dimensions, cells = parse(args.input)
    dimensions, boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    d2_integer = boundaries[2].change_ring(ZZ)
    cycle_basis = d2_integer.transpose().right_kernel_matrix()
    parity_check = cycle_basis.change_ring(GF(2))
    if parity_check.rank() != cycle_basis.nrows():
        raise AssertionError("cycle parity checks lost rank modulo two")

    lift_rows = args.lift.read_text().splitlines()
    if lift_rows[0] != "coordinate qsharp lift":
        raise ValueError("unexpected lift header")
    lift = vector(ZZ, [int(line.split()[2]) for line in lift_rows[1:]])
    if len(lift) != dimensions[2]:
        raise ValueError("lift has the wrong ambient dimension")
    syndrome = parity_check * lift.change_ring(GF(2))

    problem = MixedIntegerLinearProgram(maximization=False, solver="GLPK")
    selected = problem.new_variable(binary=True, nonnegative=True)
    halves = problem.new_variable(integer=True, nonnegative=True)
    objective = problem.sum(selected[column]
                            for column in range(dimensions[2]))
    problem.set_objective(objective)
    for row in range(parity_check.nrows()):
        support = [column for column in range(parity_check.ncols())
                   if parity_check[row, column]]
        problem.add_constraint(
            problem.sum(selected[column] for column in support)
            - 2 * halves[row] == int(syndrome[row]))
        problem.set_max(halves[row], len(support) // 2)
    candidate_weight = sum(bool(value % 2) for value in lift)
    problem.add_constraint(objective <= candidate_weight)

    optimum = int(round(problem.solve(log=2)))
    solution_values = problem.get_values(selected)
    solution_support = sorted(
        column for column, value in solution_values.items() if value > 0.5)
    solution = vector(GF(2), dimensions[2],
                      {column: 1 for column in solution_support})
    if len(solution_support) != optimum:
        raise AssertionError("binary solution weight differs from optimum")
    if parity_check * solution != syndrome:
        raise AssertionError("binary solution has the wrong syndrome")

    result = {
        "prime": prime,
        "ambient_dimension": dimensions[2],
        "range_rank": int(d2_integer.rank()),
        "parity_check_rank": int(parity_check.rank()),
        "candidate_mod2_weight": candidate_weight,
        "binary_coset_leader_weight": optimum,
        "binary_coset_leader_support": solution_support,
        "syndrome_support": [row for row, value in enumerate(syndrome) if value],
        "solver": "GLPK branch-and-bound",
        "verification": "parity_check_times_solution_equals_syndrome",
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
