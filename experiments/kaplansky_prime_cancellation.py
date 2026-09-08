#!/usr/bin/env python3
"""Exact replay of one F_3[C_3] cancellation lift, not a general proof search.

Checks a specified order-nine lift and exhausts all 243 normalized order-three
phase assignments for the same ordered blocks. The general implication is
proved in research/artifacts/kaplansky-prime-cyclic-cancellation-2026-09-07.md.
"""

import argparse
import itertools
import json
from pathlib import Path


ROWS = (0, 0, 1, 2, 2)  # Powers of the generator of C_3; occurrences repeat.
COLUMNS = (0, 1)
PIVOT = (0, 0)
BLOCKS = (
    ((4, 1), (3, 1), (1, 0)),
    ((0, 1), (2, 0), (1, 1)),
    ((3, 0), (2, 1), (4, 0)),
)
ROW_PHASES = (0, 6, 4, 2, 8)
COLUMN_PHASES = (0, 1)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reduce_phi9(coefficients):
    """Reduce an integer polynomial by z^6 + z^3 + 1, without rounding."""
    result = list(coefficients) + [0] * max(0, 6 - len(coefficients))
    for degree in range(len(result) - 1, 5, -1):
        coefficient = result[degree]
        result[degree] = 0
        result[degree - 3] -= coefficient
        result[degree - 6] -= coefficient
    return result[:6]


def lifted_product(left, right):
    """Multiply occurrence lists (C_3 power, z power) in Z[z]/Phi_9[C_3]."""
    maximum = max(a[1] + b[1] for a in left for b in right)
    coefficients = [[0] * (maximum + 1) for _ in range(3)]
    for group_left, phase_left in left:
        for group_right, phase_right in right:
            coefficients[(group_left + group_right) % 3][
                phase_left + phase_right
            ] += 1
    return [reduce_phi9(poly) for poly in coefficients]


def satisfies_phases(row_phases, column_phases, order):
    for block in BLOCKS:
        base = row_phases[block[0][0]] + column_phases[block[0][1]]
        for label, (i, j) in enumerate(block):
            difference = row_phases[i] + column_phases[j] - base
            if (difference - label * (order // 3)) % order:
                return False
    return True


def certificate():
    all_cells = list(itertools.product(range(len(ROWS)), range(len(COLUMNS))))
    listed_cells = [PIVOT] + [cell for block in BLOCKS for cell in block]
    require(sorted(listed_cells) == sorted(all_cells), "Not an exact cell partition")
    require((ROWS[PIVOT[0]] + COLUMNS[PIVOT[1]]) % 3 == 0, "Bad pivot")
    for block in BLOCKS:
        require(len(block) == 3, "Wrong block size")
        require(len({(ROWS[i] + COLUMNS[j]) % 3 for i, j in block}) == 1,
                "A block mixes group products")

    modular_product = [0, 0, 0]
    for left, right in itertools.product(ROWS, COLUMNS):
        modular_product[(left + right) % 3] += 1
    modular_product = [coefficient % 3 for coefficient in modular_product]
    require(modular_product == [1, 0, 0], "Forward modular identity failed")
    require(satisfies_phases(ROW_PHASES, COLUMN_PHASES, 9), "Order-nine lift failed")

    left = list(zip(ROWS, ROW_PHASES))
    right = list(zip(COLUMNS, COLUMN_PHASES))
    forward = lifted_product(left, right)
    reverse = lifted_product(right, left)
    identity = [[1, 0, 0, 0, 0, 0], [0] * 6, [0] * 6]
    require(forward == identity, "Forward cyclotomic identity failed")
    require(reverse == identity, "Reverse cyclotomic identity failed")

    cube_solutions = []
    assignments_checked = 0
    for values in itertools.product(range(3), repeat=5):
        assignments_checked += 1
        if satisfies_phases((0,) + values[:4], (0, values[4]), 3):
            cube_solutions.append(values)
    require(assignments_checked == 243, "Incomplete finite enumeration")
    require(not cube_solutions, "Unexpected cube-root solution")

    return {
        "schema": 1,
        "scope": "One specified ordered cancellation template in F_3[C_3].",
        "conjecture_proved": False,
        "prime": 3,
        "group": {"name": "C_3", "labels": "generator powers modulo 3"},
        "rows": list(ROWS),
        "columns": list(COLUMNS),
        "pivot": list(PIVOT),
        "blocks": [[list(cell) for cell in block] for block in BLOCKS],
        "phase_order": 9,
        "row_phase_exponents": list(ROW_PHASES),
        "column_phase_exponents": list(COLUMN_PHASES),
        "modular_forward_product": modular_product,
        "cyclotomic_relation": "z^6 + z^3 + 1 = 0",
        "cyclotomic_forward_product": forward,
        "cyclotomic_reverse_product": reverse,
        "cube_root_assignments_checked": assignments_checked,
        "cube_root_solutions": cube_solutions,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--output", type=Path)
    output.add_argument("--verify", type=Path)
    args = parser.parse_args()
    try:
        result = certificate()
        if args.verify:
            recorded = json.loads(args.verify.read_text())
            require(recorded == result, "Recorded certificate differs from exact replay")
            print("Verified the ninth-root lift and all 243 cube-root assignments.")
        elif args.output:
            args.output.write_text(json.dumps(result, indent=2) + "\n")
        else:
            print(json.dumps(result, indent=2))
    except (OSError, ValueError) as error:
        parser.exit(1, f"Verification failed: {error}\n")


if __name__ == "__main__":
    main()
