#!/usr/bin/env python3
"""Exact 16-dimensional regression certificate for global tensor amplification.

Uses only Python's standard library. This verifies one complete finite
example, not the universal proof in the accompanying Markdown artifact.
"""

from fractions import Fraction as F
from functools import reduce
from hashlib import sha256
from itertools import product
import json


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def multiply(a, b):
    columns = transpose(b)
    return [[sum((x * y for x, y in zip(row, col)), F(0))
             for col in columns] for row in a]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def subtract(a, b):
    return add(a, scale(-1, b))


def tensor(a, b):
    return [[x * y for x in ar for y in br] for ar in a for br in b]


def ldl_psd(a):
    """Return and replay an exact unpivoted LDL certificate of A >= 0."""
    assert a == transpose(a)
    n = len(a)
    lower, diagonal = eye(n), [F(0)] * n
    for j in range(n):
        diagonal[j] = a[j][j] - sum(
            (lower[j][k] ** 2 * diagonal[k] for k in range(j)), F(0))
        assert diagonal[j] >= 0, (j, diagonal[j])
        for i in range(j + 1, n):
            residual = a[i][j] - sum(
                (lower[i][k] * lower[j][k] * diagonal[k]
                 for k in range(j)), F(0))
            if diagonal[j] == 0:
                assert residual == 0
            else:
                lower[i][j] = residual / diagonal[j]
    diag_matrix = [[diagonal[i] if i == j else F(0)
                    for j in range(n)] for i in range(n)]
    assert multiply(multiply(lower, diag_matrix), transpose(lower)) == a
    return [str(x) for x in diagonal]


def digest(a):
    raw = json.dumps([[str(x) for x in row] for row in a], separators=(",", ":"))
    return sha256(raw.encode()).hexdigest()


def main():
    h = [[[F(1), F(0)], [F(0), F(0)]],
         [[F(9, 25), F(12, 25)], [F(12, 25), F(16, 25)]]]
    identity = eye(2)
    q = [subtract(identity, term) for term in h]
    assert all(multiply(term, term) == term for term in h + q)
    assert multiply(h[0], h[1]) != multiply(h[1], h[0])
    average = scale(F(1, 2), add(*h))
    epsilon = F(1, 5)
    shifted = subtract(average, scale(epsilon, identity))
    ldl_psd(shifted)
    assert shifted[0][0] * shifted[1][1] == shifted[0][1] ** 2

    # Three parallel self loops and one edge to the other vertex.
    transition = [[F(3, 4), F(1, 4)], [F(1, 4), F(3, 4)]]
    uniform = [[F(1, 2)] * 2 for _ in range(2)]
    assert multiply(subtract(transition, uniform),
                    subtract(transition, uniform)) == scale(
                        F(1, 4), subtract(identity, uniform))
    copies, dimension = 4, 16
    zero = scale(0, eye(dimension))
    acceptance, total_weight = zero, F(0)
    labelled_walks = 0
    for path in product(range(2), repeat=copies):
        multiplicity = 3 ** sum(path[j] == path[j + 1] for j in range(copies - 1))
        weight = F(multiplicity, 2 * 4 ** (copies - 1))
        labelled_walks += multiplicity
        total_weight += weight
        clause_acceptance = reduce(tensor, (q[v] for v in path))
        assert multiply(clause_acceptance, clause_acceptance) == clause_acceptance
        acceptance = add(acceptance, scale(weight, clause_acceptance))
    assert total_weight == 1 and labelled_walks == 128

    # Form the 32-dimensional transfer expression independently.
    operators = []
    for j in range(copies):
        blocks = [reduce(tensor, (q[v] if j == k else identity
                                 for k in range(copies))) for v in range(2)]
        operators.append([blocks[0][i] + zero[i] for i in range(dimension)]
                         + [zero[i] + blocks[1][i] for i in range(dimension)])
    lifted_walk = tensor(transition, eye(dimension))
    unnormalized_embedding = eye(dimension) + eye(dimension)
    transfer = operators[0]
    for operator in operators[1:]:
        transfer = multiply(multiply(transfer, lifted_walk), operator)
    transfer_acceptance = scale(F(1, 2), multiply(
        multiply(transpose(unnormalized_embedding), transfer),
        unnormalized_embedding))
    assert acceptance == transfer_acceptance

    promised_gap = 1 - (1 - epsilon) * (1 - F(3, 4) * epsilon)
    assert promised_gap == F(8, 25)
    gap_slack = subtract(scale(1 - promised_gap, eye(dimension)), acceptance)
    gap_pivots = ldl_psd(gap_slack)
    contraction_squared = 1 - F(3, 4) * epsilon
    first_step = multiply(operators[0], lifted_walk)
    contraction_slack = subtract(scale(contraction_squared, eye(32)),
                                 multiply(first_step, transpose(first_step)))
    contraction_pivots = ldl_psd(contraction_slack)
    print(json.dumps({
        "scope": "Complete exact four-copy, two-clause noncommuting example only",
        "arithmetic": "Python fractions.Fraction; no floating point",
        "input_ground_energy": str(epsilon),
        "transition_second_eigenvalue": "1/2",
        "walk_vertices": copies,
        "walk_edges": copies - 1,
        "labelled_walk_count": labelled_walks,
        "total_walk_weight": str(total_weight),
        "transfer_identity": True,
        "output_ground_energy_lower_bound": str(promised_gap),
        "acceptance_sha256": digest(acceptance),
        "gap_slack_ldl_diagonal": gap_pivots,
        "contraction_slack_ldl_diagonal": contraction_pivots,
        "all_ldl_decompositions_replayed_exactly": True,
    }, indent=2))


if __name__ == "__main__":
    main()
