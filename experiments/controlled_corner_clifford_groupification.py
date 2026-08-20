#!/usr/bin/env python3
"""Verify the finite Pauli/CZ groupification of a controlled corner.

The additive operator (1-c)+c*u is CZ when c=(1-Z1)/2 and u=Z2.
The script verifies its Pauli conjugation table and the corresponding
symplectic involution over F_2 exactly.
"""
from __future__ import annotations

import numpy as np


I2 = np.eye(2, dtype=int)
X = np.array([[0, 1], [1, 0]], dtype=int)
Z = np.array([[1, 0], [0, -1]], dtype=int)


def kron(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return np.kron(a, b)


def verify_matrix_model() -> None:
    x1, z1 = kron(X, I2), kron(Z, I2)
    x2, z2 = kron(I2, X), kron(I2, Z)
    c = (np.eye(4, dtype=int) - z1) // 2
    cz = np.eye(4, dtype=int) - c + c @ z2

    assert np.array_equal(cz, np.diag([1, 1, 1, -1]))
    assert np.array_equal(cz @ cz, np.eye(4, dtype=int))
    conjugates = {
        "X1": (cz @ x1 @ cz, x1 @ z2),
        "Z1": (cz @ z1 @ cz, z1),
        "X2": (cz @ x2 @ cz, z1 @ x2),
        "Z2": (cz @ z2 @ cz, z2),
    }
    for name, (got, want) in conjugates.items():
        if not np.array_equal(got, want):
            raise AssertionError(f"bad conjugate for {name}")


def matmul_f2(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) & 1 for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def transpose(a: list[list[int]]) -> list[list[int]]:
    return [list(row) for row in zip(*a)]


def verify_symplectic_model() -> None:
    # Coordinates are (X1,Z1,X2,Z2). Columns are the images under CZ.
    theta = [
        [1, 0, 0, 0],
        [0, 1, 1, 0],
        [0, 0, 1, 0],
        [1, 0, 0, 1],
    ]
    omega = [
        [0, 1, 0, 0],
        [1, 0, 0, 0],
        [0, 0, 0, 1],
        [0, 0, 1, 0],
    ]
    identity = [[int(i == j) for j in range(4)] for i in range(4)]
    assert matmul_f2(theta, theta) == identity
    assert matmul_f2(matmul_f2(transpose(theta), omega), theta) == omega


if __name__ == "__main__":
    verify_matrix_model()
    verify_symplectic_model()
    print("verified CZ=(1-c)+c*Z2 and its involutive Pauli automorphism")
