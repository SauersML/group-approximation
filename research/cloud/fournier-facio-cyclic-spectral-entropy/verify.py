#!/usr/bin/env python3
"""Reproduce the finite checks in NOTE.md using only the standard library."""

import cmath
import math


def matrix_rank(a: list[list[complex]], tolerance: float = 1e-9) -> int:
    a = [row[:] for row in a]
    rows, cols, rank = len(a), len(a[0]), 0
    for col in range(cols):
        pivot = max(range(rank, rows), key=lambda row: abs(a[row][col]))
        if abs(a[pivot][col]) <= tolerance:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        value = a[rank][col]
        a[rank] = [entry / value for entry in a[rank]]
        for row in range(rows):
            if row != rank:
                factor = a[row][col]
                a[row] = [x - factor * y for x, y in zip(a[row], a[rank])]
        rank += 1
        if rank == rows:
            break
    return rank


def check(phases: list[complex], weights: list[float], n: int, label: str) -> None:
    moments = [sum(w * z**k for w, z in zip(weights, phases))
               for k in range(n + 1)]
    gram = [[moments[j - i] if j >= i else moments[i - j].conjugate()
             for j in range(n + 1)] for i in range(n + 1)]
    trace_square = sum(gram[i][j] * gram[j][i]
                       for i in range(n + 1) for j in range(n + 1)).real
    formula = (n + 1) + 2 * sum(
        (n + 1 - k) * abs(moments[k]) ** 2 for k in range(1, n + 1)
    )
    assert math.isclose(trace_square, formula, abs_tol=1e-10)
    rank = matrix_rank(gram)
    lower = (n + 1) ** 2 / formula
    effective_support = 1 / sum(w * w for w in weights)
    assert rank + 1e-9 >= lower
    assert effective_support + 1e-9 >= lower
    print(label, {"rank": rank, "rank_lower_bound": lower,
                  "effective_support": effective_support})


def main() -> None:
    length = 11
    check([cmath.exp(2j * math.pi * k / length) for k in range(length)],
          [1 / length] * length, 7, "11-cycle")

    angles = [0.03, 0.19, 0.41, 0.68, 0.91]
    raw_weights = [1, 2, 4, 3, 6]
    check([cmath.exp(2j * math.pi * angle) for angle in angles],
          [weight / sum(raw_weights) for weight in raw_weights], 3,
          "five-phase nonuniform column")


if __name__ == "__main__":
    main()
