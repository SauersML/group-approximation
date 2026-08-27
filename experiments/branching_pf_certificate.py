#!/usr/bin/env python3
"""Find exact rational pressure certificates for finite branch automata.

Matrix convention: A[j][i] is the number of branches from source i to
target j.  For a strongly connected component containing a genuine branch,
this script constructs, using integer path counts only, a positive integer
vector y and rational lambda > 1 with

    A^T y >= lambda y.

Combined with a Cairn branch-capacity inequality x >= A x - e, the certificate
gives

    (lambda - 1) y.x <= y.e.

There is no numerical spectral-radius computation.  The certificate itself and
the search that constructs it are exact.
"""

import argparse
from collections import deque
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


def _integer_transpose_mul(matrix, vector):
    n = len(matrix)
    return [
        sum(matrix[j][i] * vector[j] for j in range(n))
        for i in range(n)
    ]


def path_count_certificate(block):
    """Construct the explicit certificate from recurrent path counting.

    The block is assumed strongly connected.  If every state has exactly one
    outgoing edge counting multiplicity, it is a directed cycle and there is
    no pressure above one.  Otherwise choose all branching states, compute the
    largest distance to them, and use y=sum_{t<N}(A^T)^t 1.
    """
    n = len(block)
    branching = [
        i for i in range(n)
        if sum(block[j][i] for j in range(n)) >= 2
    ]
    if not branching:
        return None

    # Reverse graph distances compute the shortest forward distance from each
    # state to any branching state.
    reverse = [[] for _ in range(n)]
    for source in range(n):
        for target in range(n):
            if block[target][source] > 0:
                reverse[target].append(source)

    distance = [None] * n
    queue = deque()
    for vertex in branching:
        distance[vertex] = 0
        queue.append(vertex)
    while queue:
        vertex = queue.popleft()
        for predecessor in reverse[vertex]:
            if distance[predecessor] is None:
                distance[predecessor] = distance[vertex] + 1
                queue.append(predecessor)
    if any(value is None for value in distance):
        raise AssertionError("component passed as strongly connected is not")

    steps = max(value + 1 for value in distance)
    current = [1] * n
    weights = [0] * n
    for _ in range(steps):
        weights = [weights[i] + current[i] for i in range(n)]
        current = _integer_transpose_mul(block, current)

    # current=(A^T)^steps 1 counts paths of the chosen length.  Every starting
    # state has reached a branching vertex and split, so all counts are >=2.
    if any(value < 2 for value in current):
        raise AssertionError("path-count branching certificate failed")

    maximum = max(weights)
    lam = Fraction(maximum + 1, maximum)
    if not verify_certificate(block, weights, lam):
        raise AssertionError("internal exact verification failed")
    return weights, lam, steps


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
        result = path_count_certificate(block)
        if result is None:
            continue
        weights, lam, steps = result
        return {
            "component": component,
            "weights": [str(v) for v in weights],
            "lambda_lower": str(lam),
            "kappa": str(lam - 1),
            "path_count_steps": steps,
        }
    return None


def self_test():
    doubled_two_cycle = [[0, 1], [2, 0]]
    neutral_two_cycle = [[0, 1], [1, 0]]
    one_state_double = [[2]]
    doubled_three_cycle = [[0, 1, 0], [0, 0, 1], [2, 0, 0]]

    certificate = find_certificate(doubled_two_cycle)
    assert certificate is not None
    assert certificate["weights"] == ["3", "2"]
    assert _fraction(certificate["lambda_lower"]) == Fraction(4, 3)
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

    certificate = find_certificate(doubled_three_cycle)
    assert certificate is not None
    assert certificate["weights"] == ["5", "4", "3"]
    assert _fraction(certificate["lambda_lower"]) == Fraction(6, 5)

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
