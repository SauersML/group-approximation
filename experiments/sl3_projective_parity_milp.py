"""Export and verify exact minimum-support mod-two Wall fillings.

The input is an exported total boundary ``d3:C3->C2``.  Binary source
variables are coupled to integer carry variables so every target coordinate
satisfies its parity equation exactly.  An optimal MILP solution therefore
certifies the minimum Hamming weight of a mod-two filling of a prescribed
two-coordinate demand.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def read_binary_boundary(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    source_rank, target_rank = map(int, lines[0].split())
    rows = [set() for _ in range(source_rank)]
    columns = [set() for _ in range(target_rank)]
    for line in lines[1:]:
        source, target, coefficient = map(int, line.split())
        if coefficient % 2 == 0:
            continue
        if target in rows[source]:
            rows[source].remove(target)
            columns[target].remove(source)
        else:
            rows[source].add(target)
            columns[target].add(source)
    return rows, columns


def linear_seed(rows: list[set[int]], target: set[int]) -> set[int]:
    """Return one exact filling using bit-parallel Gaussian elimination."""

    pivots: dict[int, tuple[int, int]] = {}
    for source, support in enumerate(rows):
        vector = sum(1 << coordinate for coordinate in support)
        combination = 1 << source
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = (vector, combination)
                break
            basis_vector, basis_combination = pivots[pivot]
            vector ^= basis_vector
            combination ^= basis_combination

    vector = sum(1 << coordinate for coordinate in target)
    combination = 0
    while vector:
        pivot = vector.bit_length() - 1
        if pivot not in pivots:
            raise ValueError("the prescribed demand is not a boundary")
        basis_vector, basis_combination = pivots[pivot]
        vector ^= basis_vector
        combination ^= basis_combination
    return {
        source for source in range(len(rows))
        if (combination >> source) & 1
    }


def verify_selected(
    rows: list[set[int]], selected: set[int], target: set[int]
) -> None:
    image: set[int] = set()
    for source in selected:
        image.symmetric_difference_update(rows[source])
    if image != target:
        raise AssertionError("the selected source vector has the wrong boundary")


def expression(variables: list[str], coefficient: str = "") -> str:
    if not variables:
        return "0"
    if coefficient:
        variables = [f"{coefficient} {variable}" for variable in variables]
    return " + ".join(variables)


def write_lp(
    boundary_path: Path,
    first_target: int,
    second_target: int,
    output_path: Path,
) -> dict:
    rows, columns = read_binary_boundary(boundary_path)
    target_rank = len(columns)
    if first_target == second_target:
        raise ValueError("the two target coordinates must be distinct")
    if not (0 <= first_target < target_rank and 0 <= second_target < target_rank):
        raise ValueError("a target coordinate is outside C2")
    right_hand_side = {first_target, second_target}
    for target in right_hand_side:
        if not columns[target]:
            raise ValueError(f"target coordinate {target} has no incoming terms")

    with output_path.open("w", encoding="utf-8") as stream:
        stream.write("Minimize\n")
        source_variables = [f"x{source}" for source in range(len(rows))]
        stream.write(" obj: " + expression(source_variables) + "\n")
        stream.write("Subject To\n")
        carry_variables = []
        for target, sources in enumerate(columns):
            rhs = 1 if target in right_hand_side else 0
            if not sources:
                if rhs:
                    raise ValueError(f"target coordinate {target} is unreachable")
                continue
            carry = f"k{target}"
            carry_variables.append((carry, (len(sources) - rhs) // 2))
            terms = [f"x{source}" for source in sorted(sources)]
            stream.write(
                f" c{target}: {expression(terms)} - 2 {carry} = {rhs}\n"
            )
        stream.write("Bounds\n")
        for carry, upper_bound in carry_variables:
            stream.write(f" 0 <= {carry} <= {upper_bound}\n")
        stream.write("Binary\n")
        for source in range(len(rows)):
            stream.write(f" x{source}\n")
        stream.write("Generals\n")
        for carry, _ in carry_variables:
            stream.write(f" {carry}\n")
        stream.write("End\n")

    return {
        "source_rank": len(rows),
        "target_rank": target_rank,
        "first_target": first_target,
        "second_target": second_target,
        "lp_path": str(output_path),
    }


def read_solution(path: Path) -> set[int]:
    selected = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) == 2:
            variable, value = fields
        elif len(fields) >= 3:
            variable, value = fields[1], fields[2]
        else:
            continue
        if not variable.startswith("x"):
            continue
        if float(value) > 0.5:
            selected.add(int(variable[1:]))
    return selected


def verify_solution(
    boundary_path: Path,
    first_target: int,
    second_target: int,
    solution_path: Path,
) -> dict:
    rows, _ = read_binary_boundary(boundary_path)
    selected = read_solution(solution_path)
    if any(source < 0 or source >= len(rows) for source in selected):
        raise AssertionError("solution contains an invalid source coordinate")
    expected = {first_target, second_target}
    verify_selected(rows, selected, expected)
    return {
        "first_target": first_target,
        "second_target": second_target,
        "minimum_support": len(selected),
        "selected_sources": sorted(selected),
        "verified": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    export_parser = subparsers.add_parser("export")
    export_parser.add_argument("boundary", type=Path)
    export_parser.add_argument("first_target", type=int)
    export_parser.add_argument("second_target", type=int)
    export_parser.add_argument("output", type=Path)

    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("boundary", type=Path)
    verify_parser.add_argument("first_target", type=int)
    verify_parser.add_argument("second_target", type=int)
    verify_parser.add_argument("solution", type=Path)

    args = parser.parse_args()
    if args.command == "export":
        result = write_lp(
            args.boundary, args.first_target, args.second_target, args.output
        )
    else:
        result = verify_solution(
            args.boundary, args.first_target, args.second_target, args.solution
        )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
