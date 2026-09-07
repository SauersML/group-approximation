#!/usr/bin/env python3
"""Verify explicit rational primal/dual certificates for syndrome synthesis.

This is a certificate replay, not a numerical SDP optimizer. The complete
primal/dual theorem and all-parameter examples are proved in the artifact.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from check_qpcp_rounding import add, multiply, outer, rational_pair, require_equal, scale, transpose
from check_qpcp_syndrome_support import (
    CertificateError, feasible_labels, flag_marginals, identity, require_psd,
    subtract, trace, verify_joint_support, verify_preparations, zero,
)


def require_size(matrix, dimension, label):
    if len(matrix) != dimension or any(len(row) != dimension for row in matrix):
        raise CertificateError(f"{label}: wrong matrix dimension")


def neighborhood_sums(terms, neighborhoods):
    if not terms or len(neighborhoods) != len(terms):
        raise CertificateError("One neighborhood per term is required")
    dimension = len(terms[0])
    for a, term in enumerate(terms):
        require_size(term, dimension, f"term {a}")
        require_psd(term, f"term {a}")
    sums = []
    for indices in neighborhoods:
        if len(indices) != len(set(indices)):
            raise CertificateError("Neighborhoods are sets, not lists with multiplicities")
        result = zero(dimension)
        for b in indices:
            if not isinstance(b, int) or not 0 <= b < len(terms):
                raise CertificateError("Invalid term index in neighborhood")
            result = add(result, terms[b])
        sums.append(result)
    return sums


def verify_primal(terms, neighborhoods, effects, c0, preparations):
    c0 = Fraction(c0)
    if c0 < 0:
        raise CertificateError("A local charge constant must be nonnegative")
    energies = neighborhood_sums(terms, neighborhoods)
    verify_joint_support(terms, effects)
    flags = flag_marginals(effects, len(terms))
    for a, (energy, flag) in enumerate(zip(energies, flags)):
        require_psd(subtract(scale(c0, energy), flag), f"local primal slack {a}")
    verify_preparations(terms, effects, preparations)
    return flags


def verify_dual(terms, neighborhoods, xs, y):
    energies = neighborhood_sums(terms, neighborhoods)
    dimension = len(terms[0])
    if len(xs) != len(terms):
        raise CertificateError("One positive dual matrix per term is required")
    for a, x in enumerate(xs):
        require_size(x, dimension, f"dual matrix {a}")
        require_psd(x, f"dual matrix {a}")
    require_size(y, dimension, "Y")
    if transpose(y) != y:
        raise CertificateError("Y must be Hermitian (real symmetric in this replay)")
    feasible = feasible_labels(terms)
    for label in feasible:
        total = zero(dimension)
        for a, x in enumerate(xs):
            if (label >> a) & 1:
                total = add(total, x)
        require_psd(subtract(total, y), f"dual slack for label {label}")
    denominator = sum(trace(multiply(x, energy)) for x, energy in zip(xs, energies))
    if denominator < 0:
        raise RuntimeError("Positive trace pairing unexpectedly became negative")
    return denominator, trace(y), feasible


def encoded(matrix):
    return [[str(Fraction(value)) for value in row] for row in matrix]


def expect_rejected(function, *args):
    try:
        function(*args)
    except CertificateError as error:
        return str(error)
    raise RuntimeError("Invalid certificate was accepted")


def replay():
    i2, z2 = identity(2), zero(2)
    paired_neighborhoods = [[0, 1], [0, 1]]
    singleton_neighborhoods = [[0], [1]]
    effects = [z2, scale(Fraction(1, 2), i2), scale(Fraction(1, 2), i2), z2]
    instances = []
    for n in (2, 3, 5, 17):
        d, s = n * n + 1, Fraction(2 * n, n * n + 1)
        p, q = rational_pair(n)
        terms = [p, q]
        xp, xq = subtract(i2, p), subtract(i2, q)
        y_impossible = scale(Fraction(1, 2), subtract(add(xp, xq), scale(s, i2)))
        denominator, numerator, feasible = verify_dual(
            terms, singleton_neighborhoods, [xp, xq], y_impossible)
        require_equal(denominator, Fraction(0), "singleton denominator")
        require_equal(numerator, Fraction((n - 1) ** 2, d), "singleton separating trace")
        if numerator <= 0:
            raise RuntimeError("The strict singleton separation disappeared")

        c0 = Fraction(d, 4)
        preparations = {1: xq, 2: xp}
        verify_primal(terms, paired_neighborhoods, effects, c0, preparations)
        ground = scale(Fraction(1, d), outer([[n], [-1]]))
        paired_denominator, paired_numerator, _ = verify_dual(
            terms, paired_neighborhoods, [ground, ground], ground)
        require_equal(paired_numerator, Fraction(1), "paired dual trace")
        require_equal(paired_denominator, Fraction(4, d), "paired dual denominator")
        require_equal(paired_numerator / paired_denominator, c0, "matching primal/dual optimum")

        too_small = expect_rejected(
            verify_primal, terms, paired_neighborhoods, effects, c0 - Fraction(1, 8), preparations)
        too_large_dual = expect_rejected(
            verify_dual, terms, paired_neighborhoods, [ground, ground], scale(2, ground))
        instances.append({
            "N": n, "feasible_fault_labels": feasible,
            "singleton_neighborhoods": {
                "X": [encoded(xp), encoded(xq)], "Y": encoded(y_impossible),
                "denominator": str(denominator), "trace_Y": str(numerator),
                "conclusion": "infeasible for every finite local charge constant",
            },
            "paired_neighborhoods": {
                "effects_by_label": [encoded(effect) for effect in effects],
                "prepared_states": {str(label): encoded(state) for label, state in preparations.items()},
                "X": [encoded(ground), encoded(ground)], "Y": encoded(ground),
                "denominator": str(paired_denominator), "trace_Y": str(paired_numerator),
                "optimal_C0": str(c0), "occurrence_R": 2, "global_C": str(2 * c0),
            },
            "negative_controls": {"smaller_primal_constant_rejected": too_small,
                                  "invalid_dual_bound_rejected": too_large_dual},
        })

    p, q = rational_pair(1)
    boundary_effects = [z2, p, q, z2]
    verify_primal([p, q], singleton_neighborhoods, boundary_effects, Fraction(1),
                  {1: subtract(i2, q), 2: subtract(i2, p)})
    boundary_q, boundary_y, _ = verify_dual([p, q], singleton_neighborhoods, [i2, i2], i2)
    require_equal(boundary_y / boundary_q, Fraction(1), "orthogonal singleton optimum")

    # A frustration-free instance permits the empty label, which excludes Y=I.
    ff_effects = [i2, z2, z2, z2]
    verify_primal([p, p], singleton_neighborhoods, ff_effects, Fraction(0),
                  {0: subtract(i2, p)})
    ff_dual_rejection = expect_rejected(
        verify_dual, [p, p], singleton_neighborhoods, [i2, i2], i2)

    names = ["check_qpcp_syndrome_sdp.py", "check_qpcp_syndrome_support.py", "check_qpcp_rounding.py"]
    return {
        "status": "passed", "arithmetic": "exact rational PSD and kernel certificates",
        "source_sha256": {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                          for name in names},
        "label_bit_order": "bit 0 flags P; bit 1 flags Q",
        "instances": instances,
        "orthogonal_N1_boundary": {"singleton_optimal_C0": "1"},
        "frustration_free_boundary": {"primal_C0": "0", "false_positive_dual_rejected": ff_dual_rejection},
        "verification_scope": "Explicit finite certificates; universal inequalities are proved in the artifact.",
        "physical_locality_of_generic_sdp_solution_proved": False,
        "quantum_pcp_proved": False, "lean_checked": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "verified_N": [row["N"] for row in result["instances"]],
                      "paired_optima": [row["paired_neighborhoods"]["optimal_C0"] for row in result["instances"]],
                      "boundary_checks": ["orthogonal", "frustration_free"],
                      "quantum_pcp_proved": False}, indent=2))


if __name__ == "__main__":
    main()
