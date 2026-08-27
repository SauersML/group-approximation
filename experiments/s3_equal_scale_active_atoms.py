#!/usr/bin/env python3
"""Audit the common spin scale of the three S3 active atoms over F_2."""

import json
from itertools import combinations, product


N = 6
PAIRS = tuple(combinations(range(N), 2))
J_FORM = (1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1)
K_FORM = (0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0)
ENDPOINTS = {
    "z1z2": (0, 0, 0, 1, 0, 1),
    "z0z2": (0, 1, 0, 0, 0, 1),
    "z0z1": (0, 1, 0, 1, 0, 0),
}


def pairing(left, right, form):
    return sum(
        value * ((left[i] & right[j]) ^ (left[j] & right[i]))
        for value, (i, j) in zip(form, PAIRS)
    ) & 1


def matrix_rank(form):
    rows = [[0] * N for _ in range(N)]
    for value, (i, j) in zip(form, PAIRS):
        rows[i][j] = rows[j][i] = value
    pivot = 0
    for column in range(N):
        found = next((row for row in range(pivot, N) if rows[row][column]), None)
        if found is None:
            continue
        rows[pivot], rows[found] = rows[found], rows[pivot]
        for row in range(N):
            if row != pivot and rows[row][column]:
                rows[row] = [a ^ b for a, b in zip(rows[row], rows[pivot])]
        pivot += 1
    return pivot


def audit():
    total = tuple(a ^ b for a, b in zip(J_FORM, K_FORM))
    vectors = tuple(product((0, 1), repeat=N))
    records = []
    for name, endpoint in ENDPOINTS.items():
        allowed_radical = all(pairing(endpoint, vector, J_FORM) == 0 for vector in vectors)
        partners = [
            index
            for index in range(N)
            if pairing(endpoint, tuple(int(index == j) for j in range(N)), total) == 1
        ]
        assert allowed_radical
        assert partners
        records.append(
            {
                "endpoint": name,
                "allowed_rank": matrix_rank(J_FORM),
                "forbidden_rank": matrix_rank(total),
                "allowed_spin_dimension": 2 ** (matrix_rank(J_FORM) // 2),
                "forbidden_spin_dimension": 2 ** (matrix_rank(total) // 2),
                "forbidden_endpoint_half_dimension": 2 ** (matrix_rank(total) // 2 - 1),
                "anticommuting_basis_partners": partners,
            }
        )
    assert all(record["allowed_spin_dimension"] == 4 for record in records)
    assert all(record["forbidden_spin_dimension"] == 8 for record in records)
    assert all(record["forbidden_endpoint_half_dimension"] == 4 for record in records)
    return {"all_checks_pass": True, "records": records}


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
