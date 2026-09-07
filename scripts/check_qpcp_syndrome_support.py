#!/usr/bin/env python3
"""Exact rational replay of joint syndrome support and conditional recovery.

This checks explicit finite witnesses. The arbitrary-measurement theorem is
proved in research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md.
No floating point, SDP solver, or third-party package is used.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from check_qpcp_rounding import (
    add, kronecker, multiply, outer, rank, rational_pair,
    require_equal, scale, transpose,
)


class CertificateError(ValueError):
    pass


def identity(dimension):
    return [[Fraction(i == j) for j in range(dimension)]
            for i in range(dimension)]


def zero(dimension):
    return scale(Fraction(0), identity(dimension))


def trace(matrix):
    return sum(matrix[i][i] for i in range(len(matrix)))


def subtract(a, b):
    return add(a, scale(-1, b))


def is_psd(matrix):
    """Exact symmetric PSD test by successive Schur complements.

    A zero diagonal in a PSD matrix forces its whole row to be zero. A
    positive pivot reduces PSD to that of its Schur complement. These two
    facts justify the algorithm, including singular matrices.
    """
    n = len(matrix)
    if n == 0 or any(len(row) != n for row in matrix):
        raise CertificateError("Expected a nonempty square matrix")
    if transpose(matrix) != matrix:
        return False
    work = [[Fraction(value) for value in row] for row in matrix]
    for k in range(n):
        pivot = work[k][k]
        if pivot < 0:
            return False
        if pivot == 0:
            if any(work[k][j] != 0 for j in range(k + 1, n)):
                return False
            continue
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                work[i][j] -= work[i][k] * work[k][j] / pivot
    return True


def require_psd(matrix, label):
    if not is_psd(matrix):
        raise CertificateError(f"{label}: matrix is not positive semidefinite")


def feasible_labels(terms):
    """Enumerate every label using the kernel of its retained positive sum."""
    dimension = len(terms[0])
    for index, term in enumerate(terms):
        require_psd(term, f"term {index}")
    result = []
    for label in range(1 << len(terms)):
        kept = zero(dimension)
        for a, term in enumerate(terms):
            if not (label >> a) & 1:
                kept = add(kept, term)
        if rank(kept) < dimension:
            result.append(label)
    return result


def verify_joint_support(terms, effects):
    dimension = len(terms[0])
    if len(effects) != 1 << len(terms):
        raise CertificateError("One effect per fault label is required")
    total = zero(dimension)
    feasible = feasible_labels(terms)
    for label, effect in enumerate(effects):
        if len(effect) != dimension or any(len(row) != dimension for row in effect):
            raise CertificateError("Effect dimension does not match the terms")
        require_psd(effect, f"effect {label}")
        total = add(total, effect)
        if label not in feasible and effect != zero(dimension):
            raise CertificateError(f"infeasible label {label} has a nonzero effect")
    require_equal(total, identity(dimension), "POVM normalization")
    return feasible


def verify_preparations(terms, effects, preparations):
    verify_joint_support(terms, effects)
    dimension = len(terms[0])
    choi_sum = zero(dimension * dimension)
    for label, effect in enumerate(effects):
        if effect == zero(dimension):
            continue
        state = preparations[label]
        require_psd(state, f"state for label {label}")
        require_equal(trace(state), Fraction(1), "state trace")
        for a, term in enumerate(terms):
            if not (label >> a) & 1:
                require_equal(multiply(term, state), zero(dimension),
                              f"label {label}: retained term {a}")
        choi = kronecker(transpose(effect), state)
        require_psd(choi, f"completely positive branch {label}")
        choi_sum = add(choi_sum, choi)
    input_marginal = [[sum(choi_sum[i * dimension + k][j * dimension + k]
                           for k in range(dimension))
                       for j in range(dimension)] for i in range(dimension)]
    require_equal(input_marginal, identity(dimension), "trace-preserving Choi marginal")


def flag_marginals(effects, number_of_terms):
    result = []
    for a in range(number_of_terms):
        marginal = zero(len(effects[0]))
        for label, effect in enumerate(effects):
            if (label >> a) & 1:
                marginal = add(marginal, effect)
        result.append(marginal)
    return result


def expect_support_rejection(terms, effects):
    try:
        verify_joint_support(terms, effects)
    except CertificateError as error:
        return str(error)
    raise RuntimeError("An infeasible positive-probability label was accepted")


def replay():
    # Normalized Bell-state density matrices; coefficients stay rational.
    good_ancilla = scale(Fraction(1, 2), outer([[0], [1], [1], [0]]))
    bad_ancilla = scale(Fraction(1, 2), outer([[1], [0], [0], [1]]))
    distributions = []
    for name, ancilla in (("good", good_ancilla), ("bad", bad_ancilla)):
        require_psd(ancilla, f"{name} ancilla")
        require_equal(trace(ancilla), Fraction(1), f"{name} ancilla trace")
        require_equal(multiply(ancilla, ancilla), ancilla, f"{name} ancilla purity")
        distributions.append([ancilla[i][i] for i in range(4)])
    require_equal(distributions[0], [0, Fraction(1, 2), Fraction(1, 2), 0],
                  "good joint distribution")
    require_equal(distributions[1], [Fraction(1, 2), 0, 0, Fraction(1, 2)],
                  "bad joint distribution")

    i2 = identity(2)
    good = [scale(probability, i2) for probability in distributions[0]]
    bad = [scale(probability, i2) for probability in distributions[1]]
    good_flags, bad_flags = flag_marginals(good, 2), flag_marginals(bad, 2)
    require_equal(good_flags, bad_flags, "identical flag marginals")
    require_equal(good_flags, [scale(Fraction(1, 2), i2)] * 2, "half-identity marginals")
    require_equal(add(*good_flags), i2, "both obey the marginal covering equality")

    instances = []
    for n in (2, 3, 5, 17):
        p, q = rational_pair(n)
        terms = [p, q]
        require_equal(feasible_labels(terms), [1, 2, 3], f"N={n}: feasible labels")
        verify_preparations(terms, good, {1: subtract(i2, q), 2: subtract(i2, p)})
        bad_rejection = expect_support_rejection(terms, bad)
        zero_port_rejection = expect_support_rejection(terms, [i2, zero(2), zero(2), zero(2)])
        c0 = Fraction(n * n + 1, 4)
        k = add(p, q)
        for a, flag in enumerate(good_flags):
            require_psd(subtract(scale(c0, k), flag), f"N={n}: neighborhood domination {a}")
        instances.append({"N": n, "feasible_fault_labels": [1, 2, 3],
                          "good_recovery": "CPTP and exact on every retained term",
                          "bad_recovery_rejected": bad_rejection,
                          "zero_port_recovery_rejected": zero_port_rejection,
                          "shared_local_cost_constant": str(c0),
                          "global_cost_bound_for_good_rounder": str(2 * c0)})

    paths = [Path(__file__), Path(__file__).with_name("check_qpcp_rounding.py")]
    return {"status": "passed", "arithmetic": "exact rational matrices",
            "source_sha256": {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
            "label_bit_order": "bit 0 flags P; bit 1 flags Q",
            "good_joint_probabilities": [str(x) for x in distributions[0]],
            "bad_joint_probabilities": [str(x) for x in distributions[1]],
            "instances": instances,
            "scope": "Explicit two-term examples; universal support and dilation proofs are in the artifact.",
            "quantum_pcp_proved": False, "lean_checked": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rendered = json.dumps(replay(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
