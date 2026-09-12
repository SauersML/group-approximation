#!/usr/bin/env python3
"""Exact finite checks for the flexible HS metric and padding proof.

All arithmetic is rational. The sample matrices are real orthogonal, hence
unitary. These finite checks do not establish the all-dimensions theorem;
its written proof is research/artifacts/flexible-hs-metric-and-padding.md.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path

Matrix = tuple[tuple[Q, ...], ...]
ROOT = Path(__file__).resolve().parents[1]


def identity(n: int) -> Matrix:
    if n < 1:
        raise ValueError("Matrix dimension must be positive")
    return tuple(tuple(Q(i == j) for j in range(n)) for i in range(n))


def diagonal(entries) -> Matrix:
    entries = tuple(map(Q, entries))
    return tuple(tuple(entries[i] if i == j else Q(0)
                       for j in range(len(entries))) for i in range(len(entries)))


def transpose(a: Matrix) -> Matrix:
    return tuple(zip(*a))


def multiply(a: Matrix, b: Matrix) -> Matrix:
    if len(a) != len(b):
        raise ValueError("Matrix products must have the same dimension")
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(len(a)))
                       for j in range(len(a))) for i in range(len(a)))


def require_unitary(a: Matrix) -> None:
    n = len(a)
    if not n or any(len(row) != n for row in a):
        raise ValueError("Expected a nonempty square matrix")
    if multiply(transpose(a), a) != identity(n):
        raise ValueError("Matrix is not exactly orthogonal")


def extend(a: Matrix, n: int, *, trivial: bool = False) -> Matrix:
    d = len(a)
    if n < d:
        raise ValueError("Cannot extend to a smaller dimension")
    return tuple(tuple(a[i][j] if i < d and j < d else
                       Q(trivial and i == j and i >= d)
                       for j in range(n)) for i in range(n))


def frobenius_squared(a: Matrix) -> Q:
    return sum((entry * entry for row in a for entry in row), Q(0))


def difference(a: Matrix, b: Matrix) -> Matrix:
    if len(a) != len(b):
        raise ValueError("Matrix differences must have the same dimension")
    return tuple(tuple(x - y for x, y in zip(ar, br)) for ar, br in zip(a, b))


def distance_squared(a: Matrix, b: Matrix) -> Q:
    n = max(len(a), len(b))
    return frobenius_squared(difference(extend(a, n), extend(b, n))) / n


def sqrt_triangle_holds(ab: Q, bc: Q, ac: Q) -> bool:
    """Decide sqrt(ac) <= sqrt(ab)+sqrt(bc) without approximation."""
    if min(ab, bc, ac) < 0:
        raise ValueError("Squared distances cannot be negative")
    remainder = ac - ab - bc
    return remainder <= 0 or remainder * remainder <= 4 * ab * bc


def word_value(generators: tuple[Matrix, ...], word: tuple[int, ...]) -> Matrix:
    value = identity(len(generators[0]))
    for letter in word:
        if letter == 0 or abs(letter) > len(generators):
            raise ValueError("Invalid generator index")
        factor = generators[abs(letter) - 1]
        value = multiply(value, factor if letter > 0 else transpose(factor))
    return value


def signed_permutation(p, signs) -> Matrix:
    return tuple(tuple(Q(signs[i] if j == p[i] else 0)
                       for j in range(len(p))) for i in range(len(p)))


def sample_matrices() -> list[Matrix]:
    result = [signed_permutation(p, s)
              for n in range(1, 4)
              for p in permutations(range(n))
              for s in product((-1, 1), repeat=n)]
    result.append(((Q(3, 5), Q(-4, 5)), (Q(4, 5), Q(3, 5))))
    for a in result:
        require_unitary(a)
    return result


def sample_tuples() -> list[tuple[Matrix, Matrix]]:
    rot = ((Q(3, 5), Q(-4, 5)), (Q(4, 5), Q(3, 5)))
    swap = signed_permutation((1, 0), (1, 1))
    cycle = signed_permutation((1, 2, 0), (1, 1, 1))
    result = [
        (identity(1), diagonal([-1])),
        (diagonal([-1]), identity(1)),
        (rot, diagonal([1, -1])),
        (swap, diagonal([-1, 1])),
        (extend(rot, 3, trivial=True), cycle),
        (cycle, diagonal([1, -1, 1])),
        (extend(rot, 4, trivial=True), diagonal([1, 1, -1, 1])),
    ]
    for pair in result:
        for a in pair:
            require_unitary(a)
    return result


def tuple_distance_squared(a, b) -> Q:
    return max(distance_squared(x, y) for x, y in zip(a, b))


def compression_terms(u: Matrix, v: Matrix) -> tuple[Q, Q, Q]:
    """Dimension, compression, and leakage terms in equation (6)/D."""
    d, n = len(u), len(v)
    if d > n:
        raise ValueError("Compression requires dim(u) <= dim(v)")
    a = tuple(tuple(v[i][j] for j in range(d)) for i in range(d))
    compression = frobenius_squared(difference(u, a)) / n
    leakage = sum((v[i][j] ** 2 for i in range(d, n) for j in range(d)), Q(0)) / n
    return Q(n - d, n), compression, leakage


def diagonal_identity_distance_squared(entries: tuple[int, ...], n: int) -> Q:
    d = len(entries)
    return sum((Q(entries[i] if i < d else 0) - Q(i < n)) ** 2
               for i in range(max(d, n))) / max(d, n)


def sharp_family_formula(d: int, k: int, n: int) -> Q:
    if not (d > 4 * k >= 4 and n >= 1):
        raise ValueError("Sharpness family requires d > 4k >= 4 and n >= 1")
    if n <= d - k:
        return Q(d - n, d)
    if n <= d:
        return Q(3 * n - 3 * d + 4 * k, d)
    return 1 - Q(d - 4 * k, n)


def replay() -> dict:
    matrices = sample_matrices()
    distances = [[distance_squared(a, b) for b in matrices] for a in matrices]
    triangles = 0
    for i, j, k in product(range(len(matrices)), repeat=3):
        if not sqrt_triangle_holds(distances[i][j], distances[j][k], distances[i][k]):
            raise ValueError(f"Triangle failure at matrix indices {(i, j, k)}")
        triangles += 1

    dimensions = compressions = leaking_compressions = 0
    for i, a in enumerate(matrices):
        for j, b in enumerate(matrices):
            charge = Q(abs(len(a) - len(b)), max(len(a), len(b)))
            if distances[i][j] < charge:
                raise ValueError("Dimension charge failed")
            dimensions += 1
            if len(a) <= len(b):
                terms = compression_terms(a, b)
                if sum(terms) != distances[i][j]:
                    raise ValueError("Compression identity failed")
                compressions += 1
                leaking_compressions += int(terms[2] > 0)

    tuples = sample_tuples()
    words = [(), (1,), (2,), (-1,), (1, 2), (1, 2, -1, -2),
             (1, 2, 1), (2, -1, 2, 1, -2)]
    word_checks = defect_checks = upward_checks = 0
    defect_words = [((1, 2), (2, 1)), ((1, 2, -1, -2), ()), ((1,), (-2,))]
    lipschitz = max(max(1, len(a)) + max(1, len(b)) for a, b in defect_words)
    for u, v in product(tuples, repeat=2):
        delta = tuple_distance_squared(u, v)
        for word in words:
            actual = distance_squared(word_value(u, word), word_value(v, word))
            if actual > max(1, len(word)) ** 2 * delta:
                raise ValueError("Word Lipschitz bound failed")
            word_checks += 1
        eu, ev = [max(distance_squared(word_value(t, a), word_value(t, b))
                      for a, b in defect_words) for t in (u, v)]
        if not (sqrt_triangle_holds(eu, lipschitz ** 2 * delta, ev)
                and sqrt_triangle_holds(ev, lipschitz ** 2 * delta, eu)):
            raise ValueError("Cross-dimension defect Lipschitz bound failed")
        defect_checks += 1
        d, n = len(u[0]), len(v[0])
        target = tuple(extend(a, d, trivial=True) for a in v) if n < d else v
        if tuple_distance_squared(u, target) > 4 * delta:
            raise ValueError("Upward conversion bound failed")
        upward_checks += 1

    family_checks = family_count = 0
    for d in range(5, 21):
        for k in range(1, (d - 1) // 4 + 1):
            entries = (1,) * (d - k) + (-1,) * k
            values = {}
            for n in range(1, 2 * d + 1):
                actual = diagonal_identity_distance_squared(entries, n)
                if actual != sharp_family_formula(d, k, n):
                    raise ValueError("Sharp-family formula failed")
                values[n] = actual
                family_checks += 1
            if min(values.values()) != Q(k, d):
                raise ValueError("Unrestricted finite-sample minimum failed")
            if min(value for n, value in values.items() if n >= d) != Q(4 * k, d):
                raise ValueError("Upward finite-sample minimum failed")
            family_count += 1

    a, b, x, y = diagonal([-1, 1]), identity(2), diagonal([-1]), identity(1)
    audit = {
        "larger_pair_defect_squared": str(distance_squared(a, b)),
        "smaller_pair_defect_squared": str(distance_squared(x, y)),
        "plus_comparison_distance_squared": str(distance_squared(a, x)),
        "minus_comparison_distance_squared": str(distance_squared(b, y)),
        "smaller_defect_after_common_normalization_squared": str(
            frobenius_squared(difference(extend(x, 2), extend(y, 2))) / 2),
    }
    return {
        "schema_version": 1,
        "status": "pass",
        "arithmetic": "fractions.Fraction; no floating-point tolerances",
        "scope": "Finite rational orthogonal examples; general theorem is a written proof, not Lean-verified.",
        "checks": {
            "unitary_matrices": len(matrices),
            "ordered_triangle_cases": triangles,
            "dimension_charge_cases": dimensions,
            "compression_identity_cases": compressions,
            "compression_cases_with_nonzero_leakage": leaking_compressions,
            "word_cases_including_empty_word": word_checks,
            "cross_dimension_local_defect_cases": defect_checks,
            "upward_conversion_cases": upward_checks,
            "sharp_families": family_count,
            "sharp_formula_cases": family_checks,
        },
        "normalization_audit": audit,
        "sharpness_scope": "d=5..20, 1<=k<d/4, D=1..2d; global infima follow from the proof's monotonicity argument.",
        "source_sha256": {
            "experiments/flexible_hs_metric_audit.py": sha256(Path(__file__).read_bytes()).hexdigest(),
            "research/artifacts/flexible-hs-metric-and-padding.md": sha256(
                (ROOT / "research/artifacts/flexible-hs-metric-and-padding.md").read_bytes()).hexdigest(),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-out", type=Path)
    parser.add_argument("--compare-report", type=Path)
    args = parser.parse_args()
    report = replay()
    if args.compare_report and json.loads(args.compare_report.read_text()) != report:
        raise ValueError("Committed report differs from exact replay")
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.report_out:
        args.report_out.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
