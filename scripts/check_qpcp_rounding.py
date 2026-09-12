#!/usr/bin/env python3
"""Exact replay for the paired-projector rounder obstruction; stdlib only.

Polynomial coefficient equality checks the displayed identities for every N.
Full rational tensor matrices separately exhaust fault sets for N <= 3.
The all-size and instrument proofs are in the accompanying research artifact.
This is neither a Lean certificate nor a proof of quantum PCP.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path


@dataclass(frozen=True)
class Poly:
    """Integer polynomial, coefficients in ascending degree order."""

    coefficients: tuple[int, ...]

    def __post_init__(self):
        values = list(self.coefficients)
        while len(values) > 1 and values[-1] == 0:
            values.pop()
        object.__setattr__(self, "coefficients", tuple(values or [0]))

    @staticmethod
    def of(value):
        return value if isinstance(value, Poly) else Poly((value,))

    def __add__(self, other):
        other = Poly.of(other)
        a, b = self.coefficients, other.coefficients
        return Poly(tuple((a[i] if i < len(a) else 0)
                          + (b[i] if i < len(b) else 0)
                          for i in range(max(len(a), len(b)))))

    __radd__ = __add__

    def __neg__(self):
        return Poly(tuple(-value for value in self.coefficients))

    def __sub__(self, other):
        return self + (-Poly.of(other))

    def __rsub__(self, other):
        return Poly.of(other) + (-self)

    def __mul__(self, other):
        other = Poly.of(other)
        result = [0] * (len(self.coefficients) + len(other.coefficients) - 1)
        for i, a in enumerate(self.coefficients):
            for j, b in enumerate(other.coefficients):
                result[i + j] += a * b
        return Poly(tuple(result))

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("Polynomial powers must be nonnegative integers")
        result = Poly.of(1)
        for _ in range(exponent):
            result = result * self
        return result


def require_equal(actual, expected, label):
    # Explicit exception, so python -O cannot silently disable verification.
    if actual != expected:
        raise RuntimeError(f"{label}: {actual!r} != {expected!r}")


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(factor, matrix):
    return [[factor * entry for entry in row] for row in matrix]


def multiply(a, b):
    return [[sum(x * y for x, y in zip(row, column))
             for column in transpose(b)] for row in a]


def outer(vector):
    return multiply(vector, transpose(vector))


def determinant2(matrix):
    return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]


def symbolic_checks():
    n = Poly((0, 1))
    d = n**2 + 1
    p = [[Poly.of(0), Poly.of(0)], [Poly.of(0), Poly.of(1)]]
    u = [[2 * n], [n**2 - 1]]
    q_num = outer(u)  # Q = q_num / d^2.
    k_num = add(scale(d**2, p), q_num)
    g, f = [[n], [Poly.of(-1)]], [[Poly.of(1)], [n]]
    checks = [
        ("unit-vector numerator", multiply(transpose(u), u), [[d**2]]),
        ("P is a projector", multiply(p, p), p),
        ("Q projector identity", multiply(q_num, q_num), scale(d**2, q_num)),
        ("ground eigenvector", multiply(k_num, g), scale(2 * d, g)),
        ("upper eigenvector", multiply(k_num, f), scale(2 * n**2 * d, f)),
        ("eigenvectors orthogonal", multiply(transpose(g), f), [[Poly.of(0)]]),
        ("ground vector norm", multiply(transpose(g), g), [[d]]),
        ("upper vector norm", multiply(transpose(f), f), [[d]]),
        ("complete spectral decomposition", k_num,
         add(scale(2, outer(g)), scale(2 * n**2, outer(f)))),
        ("positive pair determinant numerator", determinant2(k_num),
         4 * n**2 * d**2),
    ]
    for label, actual, expected in checks:
        require_equal(actual, expected, label)
    return [label for label, _, _ in checks]


def rational_pair(n):
    if not isinstance(n, int) or n < 1:
        raise ValueError("N must be a positive integer")
    d = n * n + 1
    p = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(1)]]
    u = [[Fraction(2 * n, d)], [Fraction(n * n - 1, d)]]
    return p, outer(u)


def kronecker(a, b):
    return [[a[i][j] * b[k][ell]
             for j in range(len(a[0])) for ell in range(len(b[0]))]
            for i in range(len(a)) for k in range(len(b))]


def embed(term, site, n):
    identity = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]
    matrix = [[Fraction(1)]]
    for j in range(n):
        matrix = kronecker(matrix, term if j == site else identity)
    return matrix


def rank(matrix):
    """Exact rational Gaussian elimination, with no tolerance decisions."""
    rows = [list(row) for row in matrix]
    pivot_row = 0
    for column in range(len(rows[0])):
        candidate = next((i for i in range(pivot_row, len(rows))
                          if rows[i][column] != 0), None)
        if candidate is None:
            continue
        rows[pivot_row], rows[candidate] = rows[candidate], rows[pivot_row]
        pivot = rows[pivot_row][column]
        rows[pivot_row] = [value / pivot for value in rows[pivot_row]]
        for i in range(pivot_row + 1, len(rows)):
            factor = rows[i][column]
            rows[i] = [x - factor * y for x, y in zip(rows[i], rows[pivot_row])]
        pivot_row += 1
        if pivot_row == len(rows):
            break
    return pivot_row


def exhaustive_fault_sets(terms):
    """Replay every subset; the common kernel equals the kernel of the PSD sum."""
    dimension = len(terms[0])
    feasible_counts = {}
    for faults in range(1 << len(terms)):
        kept = [[Fraction(0) for _ in range(dimension)] for _ in range(dimension)]
        for i, term in enumerate(terms):
            if not (faults >> i) & 1:
                kept = add(kept, term)
        if rank(kept) < dimension:
            size = faults.bit_count()
            feasible_counts[size] = feasible_counts.get(size, 0) + 1
    return {
        "fault_sets_examined": 1 << len(terms),
        "hilbert_space_dimension": dimension,
        "minimum_fault_count": min(feasible_counts),
        "feasible_counts_by_cardinality": feasible_counts,
    }


def certificate():
    identities = symbolic_checks()
    instances = []
    for n in (1, 2, 3, 8, 31, 100):
        p, q = rational_pair(n)
        k = add(p, q)
        d = n * n + 1
        g = [[Fraction(n)], [Fraction(-1)]]
        require_equal(multiply(p, p), p, f"N={n}: P projector")
        require_equal(multiply(q, q), q, f"N={n}: Q projector")
        require_equal(transpose(q), q, f"N={n}: Q self-adjoint")
        require_equal(multiply(k, g), scale(Fraction(2, d), g),
                      f"N={n}: ground eigenvector")
        energy = multiply(transpose(g), multiply(k, g))[0][0] / (2 * d)
        require_equal(energy, Fraction(1, d), f"N={n}: normalized energy")
        cost = Fraction(n) / (2 * n * energy)
        require_equal(cost, Fraction(d, 2), f"N={n}: sharp cost")
        instances.append({"N": n, "energy_density": str(energy),
                          "optimal_rounder_cost": str(cost),
                          "singleton_port_cover_deficit": str(1 - 2 * energy)})

    exhaustions = []
    for n in (1, 2, 3):
        p, q = rational_pair(n)
        terms = [embed(term, j, n) for j in range(n) for term in (p, q)]
        result = exhaustive_fault_sets(terms)
        require_equal(result["minimum_fault_count"], n, f"N={n}: exact defect")
        exhaustions.append({"N": n, **result})

    p, _ = rational_pair(1)
    zero_energy_case = exhaustive_fault_sets([p, p])
    require_equal(zero_energy_case["minimum_fault_count"], 0,
                  "frustration-free pair has an empty feasible fault set")
    require_equal(multiply(p, [[Fraction(1)], [Fraction(0)]]),
                  [[Fraction(0)], [Fraction(0)]], "zero-cost preparation witness")
    return {
        "status": "passed",
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "arithmetic": "integer polynomial coefficients and exact rational matrices",
        "universal_polynomial_identities": identities,
        "exact_instance_checks": instances,
        "complete_finite_fault_exhaustions": exhaustions,
        "zero_energy_regression": {**zero_energy_case, "optimal_rounder_cost": "0"},
        "boundary": {
            "all_size_instrument_argument": "ordinary proof in the accompanying artifact",
            "finite_exhaustion_max_N": 3,
            "lean_checked": False,
            "wolfram_executed": False,
            "quantum_pcp_proved": False,
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Also save the JSON certificate here")
    args = parser.parse_args()
    rendered = json.dumps(certificate(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
