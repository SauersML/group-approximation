#!/usr/bin/env python3
"""Check the finite-stage identities in the BS(1,2) fiber-swap model."""

from __future__ import annotations

import argparse
import math

import numpy as np


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right @ left.conj().T @ right.conj().T


def errors(m: int) -> tuple[float, float, float, float]:
    size = 2 * m
    zeta = np.exp(1j * math.pi / m)
    parent = np.diag(zeta ** np.arange(size))

    shuffle = np.zeros((size, size), dtype=np.complex128)
    for r in range(m):
        shuffle[r, 2 * r] = 1
        shuffle[m + r, 2 * r + 1] = 1
    child = shuffle @ parent @ shuffle.conj().T

    swap = np.zeros((size, size), dtype=np.complex128)
    for r in range(m):
        swap[m + r, r] = 1
        swap[r, m + r] = 1

    identity = np.eye(size, dtype=np.complex128)
    relation = np.linalg.norm(child - parent @ parent, ord=2)
    square_commutation = np.linalg.norm(
        commutator(swap, parent @ parent) - identity, ord=2
    )
    child_commutation = np.linalg.norm(
        commutator(swap, child) - identity, ord=2
    )
    marked_distance = np.linalg.norm(
        commutator(swap, parent) - identity, ord=2
    )
    return relation, square_commutation, child_commutation, marked_distance


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("m", nargs="*", type=int, default=[4, 8, 16, 32, 64])
    args = parser.parse_args()

    print("m  relation error  square commutator  child commutator  marked distance")
    for m in args.m:
        if m < 2:
            raise SystemExit("m must be at least 2")
        relation, square, child, marked = errors(m)
        predicted = 2 * math.sin(math.pi / (2 * m))
        if not math.isclose(relation, predicted, rel_tol=1e-10, abs_tol=1e-12):
            raise AssertionError((m, relation, predicted))
        if not math.isclose(child, predicted, rel_tol=1e-10, abs_tol=1e-12):
            raise AssertionError((m, child, predicted))
        if square > 1e-12 or not math.isclose(marked, 2.0, abs_tol=1e-12):
            raise AssertionError((m, square, marked))
        print(
            f"{m:2d} {relation:15.12f} {square:18.3e} "
            f"{child:18.12f} {marked:16.12f}"
        )


if __name__ == "__main__":
    main()
