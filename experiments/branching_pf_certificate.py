#!/usr/bin/env python3
"""Find exact rational supercriticality certificates for finite branch automata.

Matrix convention: A[j][i] is the number of branches from source i to
target j. A certificate is a positive rational vector y and lambda > 1 with

    A^T y >= lambda y.

Combined with a Cairn branch-capacity inequality x >= A x - e, this certifies

    (lambda - 1) y.x <= y.e,

so positive y-weighted carrier mass is incompatible with vanishing error.

The floating-point power iteration below is proposal-only. Every emitted
certificate is rechecked exactly with fractions.Fraction.
"""

import argparse
from fractions import Fraction
import json
import sys


def _fraction(value):
    if isinstance(value, Fraction):
        return value
    return Fraction(str(value))


def transpose_mul(matrix, vector):
    n = len(matrix)
    return [
        sum(Fraction(matrix[j][i]) * vector[j] for j in range(n))
        for i in range(n)
    ]


def verify_certificate(matrix, weights, lam):
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("matrix must be square")
    if len(weights) != n:
        raise ValueError("weight vector has wrong length")
    weights = [_fraction(v) for v in weights]
    lam = _fraction(lam)
    if lam <= 1 or any(v <= 0 for v in weights):
        return False
    lhs = transpose_mul(matrix, weights)
    return all(lhs[i] >= lam * weights[i] for i in range(n))


def tarjan_scc(matrix):
    """Strongly connected components for edges i -> j when A[j][i] > 0."""
    n = len(matrix)
    adjacency = [
        [j for j in range(n) if matrix[j][i] > 0]
        for i in range(n)
    ]
    index = 0
    stack = []
    on_stack = set()
    indices = [None] * n
    lowlink = [0] * n
    components = []

    def visit(v):
        nonlocal index
        indices[v] = lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)

        for w in adjacency[v]:
            if indices[w] is None:
                visit(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])

        if lowlink[v] == indices[v]:
            component = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                component.append(w)
                if w == v:
                    break
            components.append(sorted(component))

    for v in range(n):
        if indices[v] is None:
            visit(v)
    return components


def _submatrix(matrix, component):
    return [
        [matrix[j][i] for i in component]
        for j in component
    ]


def propose_integer_weights(matrix, iterations=256, scale=1_000_000):
    """Power iterate (I+A)^T only to propose an integer positive vector."""
    n = len(matrix)
    y = [1.0] * n
    for _ in range(iterations):
        z = []
        for i in range(n):
            z.append(y[i] + sum(matrix[j][i] * y[j] for j in range(n)))
        maximum = max(z, default=0.0)
        if maximum <= 0:
            break
        y = [value / maximum for value in z]
    return [max(1, int(round(value * scale))) for value in y]


def exact_lambda_lower(matrix, weights):
    weights = [Fraction(v) for v in weights]
    lhs = transpose_mul(matrix, weights)
    return min(lhs[i] / weights[i] for i in range(len(weights)))


def find_certificate(matrix):
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("matrix must be square")
    if any((not isinstance(v, int)) or v < 0 for row in matrix for v in row):
        raise ValueError("branch matrix entries must be nonnegative integers")

    for component in tarjan_scc(matrix):
        if len(component) == 1 and matrix[component[0]][component[0]] == 0:
            continue
        block = _submatrix(matrix, component)
        weights = propose_integer_weights(block)
        lam = exact_lambda_lower(block, weights)
        if lam <= 1:
            continue
        if not verify_certificate(block, weights, lam):
            raise AssertionError("internal exact verification failed")
        return {
            "component": component,
            "weights": [str(v) for v in weights],
            "lambda_lower": str(lam),
            "kappa": str(lam - 1),
        }
    return None


def self_test():
    doubled_two_cycle = [[0, 1], [2, 0]]
    neutral_two_cycle = [[0, 1], [1, 0]]
    one_state_double = [[2]]

    certificate = find_certificate(doubled_two_cycle)
    assert certificate is not None
    assert _fraction(certificate["lambda_lower"]) > 1
    assert verify_certificate(
        _submatrix(doubled_two_cycle, certificate["component"]),
        certificate["weights"],
        certificate["lambda_lower"],
    )

    assert find_certificate(neutral_two_cycle) is None

    certificate = find_certificate(one_state_double)
    assert certificate is not None
    assert _fraction(certificate["lambda_lower"]) == 2
    assert _fraction(certificate["kappa"]) == 1

    print("branching_pf_certificate self-test: ok")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "matrix",
        nargs="?",
        help="JSON file containing a square nonnegative integer matrix",
    )
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        self_test()
        return 0
    if not args.matrix:
        parser.error("provide MATRIX.json or --self-test")

    with open(args.matrix, encoding="utf-8") as handle:
        matrix = json.load(handle)
    certificate = find_certificate(matrix)
    payload = {
        "matrix_convention": "A[j][i] counts branches source i -> target j",
        "certificate": certificate,
    }
    print(json.dumps(payload, indent=2))
    return 0 if certificate is not None else 2


if __name__ == "__main__":
    sys.exit(main())
