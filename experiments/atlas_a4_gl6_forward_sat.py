#!/usr/bin/env python3
"""Solve the exact GL6(F2) one-forward-context problem with Z3.

The packet instance is read as JSON on standard input.  Matrix entries are
Boolean variables, multiplication is XOR-of-AND over F2, and a second matrix
is constrained to be the two-sided inverse.  ``--escape`` additionally asks
that the relative frame fail to commute with at least one rank-three
generator.  A SAT model is rechecked by the independent exact matrix scripts.
"""

import argparse
import json
import sys

import z3


DIMENSION = 6


def xor_all(terms):
    if not terms:
        return z3.BoolVal(False)
    if len(terms) == 1:
        return terms[0]
    value = terms[0]
    for term in terms[1:]:
        value = z3.Xor(value, term)
    return value


def multiply(left, right):
    return [
        [
            xor_all([z3.And(left[row][k], right[k][column]) for k in range(DIMENSION)])
            for column in range(DIMENSION)
        ]
        for row in range(DIMENSION)
    ]


def identity():
    return [
        [z3.BoolVal(row == column) for column in range(DIMENSION)]
        for row in range(DIMENSION)
    ]


def embed4(matrix):
    return [
        [
            z3.BoolVal(
                bool(matrix[row][column])
                if row < 4 and column < 4
                else row == column
            )
            for column in range(DIMENSION)
        ]
        for row in range(DIMENSION)
    ]


def equalities(left, right):
    return [
        left[row][column] == right[row][column]
        for row in range(DIMENSION)
        for column in range(DIMENSION)
    ]


def word_value(word, relative, relative_inverse):
    value = identity()
    for factor, matrix in word:
        image = embed4(matrix)
        if factor == 2:
            image = multiply(multiply(relative, image), relative_inverse)
        value = multiply(value, image)
    return value


def cube(value):
    return multiply(multiply(value, value), value)


def model_hex(model, matrix):
    return "".join(
        "01" if z3.is_true(model.evaluate(matrix[row][column], model_completion=True)) else "00"
        for row in range(DIMENSION)
        for column in range(DIMENSION)
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--escape", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=600000)
    args = parser.parse_args()
    instance = json.load(sys.stdin)

    relative = [
        [z3.Bool(f"h_{row}_{column}") for column in range(DIMENSION)]
        for row in range(DIMENSION)
    ]
    relative_inverse = [
        [z3.Bool(f"k_{row}_{column}") for column in range(DIMENSION)]
        for row in range(DIMENSION)
    ]
    solver = z3.Solver()
    solver.set(timeout=args.timeout_ms)
    solver.add(*equalities(multiply(relative, relative_inverse), identity()))
    solver.add(*equalities(multiply(relative_inverse, relative), identity()))

    for word in instance["core"]:
        solver.add(*equalities(cube(word_value(word, relative, relative_inverse)), identity()))
    solver.add(*equalities(
        word_value(instance["collision"], relative, relative_inverse),
        identity(),
    ))
    solver.add(*equalities(
        cube(word_value(instance["forward"], relative, relative_inverse)),
        identity(),
    ))

    if args.escape:
        moved_entries = []
        for generator in instance["rank_three_generators"]:
            image = embed4(generator)
            left = multiply(relative, image)
            right = multiply(image, relative)
            moved_entries.extend(
                z3.Xor(left[row][column], right[row][column])
                for row in range(DIMENSION)
                for column in range(DIMENSION)
            )
        solver.add(z3.Or(*moved_entries))

    result = solver.check()
    output = {
        "dimension": DIMENSION,
        "escape_required": args.escape,
        "result": str(result),
        "solver_statistics": str(solver.statistics()),
    }
    if result == z3.sat:
        model = solver.model()
        output["relative_matrix_hex"] = model_hex(model, relative)
        output["relative_inverse_hex"] = model_hex(model, relative_inverse)
    elif result == z3.unknown:
        output["reason_unknown"] = solver.reason_unknown()
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
