#!/usr/bin/env python3
"""Replay exact certificates for syndrome kernel resolutions and their failure.

No search completeness or QPCP proof is asserted. General theorems are
proved in research/artifacts/qpcp-kernel-resolution-2026-09-07.md.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from check_qpcp_rounding import (
    add, embed, kronecker, multiply, outer, rank, rational_pair,
    require_equal, scale, transpose,
)
from check_qpcp_syndrome_support import (
    CertificateError, feasible_labels, identity, require_psd,
    subtract, trace, verify_joint_support, zero,
)
from check_qpcp_syndrome_sdp import (
    encoded, expect_rejected, neighborhood_sums, require_size,
    verify_dual, verify_primal,
)


def verify_range_projection(matrix, projection):
    dimension = len(matrix)
    require_size(projection, dimension, "range projection")
    require_psd(matrix, "positive operator")
    require_psd(projection, "range projection")
    require_equal(multiply(projection, projection), projection, "projection idempotence")
    require_equal(multiply(projection, matrix), matrix, "operator range inclusion")
    require_equal(rank(projection), rank(matrix), "range dimension equality")


def verify_kernel_resolution(terms, neighborhoods, effects, ranges):
    energies = neighborhood_sums(terms, neighborhoods)
    if len(ranges) != len(terms):
        raise CertificateError("One range projector per energy neighborhood is required")
    for energy, projection in zip(energies, ranges):
        verify_range_projection(energy, projection)
    verify_joint_support(terms, effects)
    for label, effect in enumerate(effects):
        for a, projection in enumerate(ranges):
            if (label >> a) & 1 and multiply(projection, effect) != effect:
                raise CertificateError(f"label {label}: effect escapes charged range {a}")
    return energies


def verify_spectral_bound(energies, ranges, delta):
    delta = Fraction(delta)
    if delta <= 0:
        raise CertificateError("A spectral bound must be strictly positive")
    if len(energies) != len(ranges):
        raise CertificateError("One range projection per energy operator is required")
    for a, (energy, projection) in enumerate(zip(energies, ranges)):
        verify_range_projection(energy, projection)
        require_psd(subtract(energy, scale(delta, projection)), f"local spectral slack {a}")


def verify_support_separator(terms, neighborhoods, ranges, supports, y):
    energies = neighborhood_sums(terms, neighborhoods)
    dimension = len(terms[0])
    if len(ranges) != len(terms):
        raise CertificateError("Range projector count does not match")
    for energy, projection in zip(energies, ranges):
        verify_range_projection(energy, projection)
    require_size(y, dimension, "separator")
    if transpose(y) != y or trace(y) <= 0:
        raise CertificateError("Separator must be Hermitian with positive trace")
    feasible = feasible_labels(terms)
    if sorted(supports) != feasible:
        raise CertificateError("One support projector per feasible label is required")
    support_sum = zero(dimension)
    for label in feasible:
        v = supports[label]
        require_size(v, dimension, "input support projector")
        require_psd(v, "input support projector")
        require_equal(multiply(v, v), v, "support projection idempotence")
        kernel_sum = zero(dimension)
        for a, projection in enumerate(ranges):
            if (label >> a) & 1:
                kernel_sum = add(kernel_sum, subtract(identity(dimension), projection))
        require_equal(multiply(kernel_sum, v), zero(dimension), "support kernel inclusion")
        require_equal(rank(v), dimension - rank(kernel_sum), "support kernel dimension")
        require_psd(scale(-1, multiply(multiply(v, y), v)), f"separator compression {label}")
        support_sum = add(support_sum, v)
    return rank(support_sum)


def replay():
    i2, z2 = identity(2), zero(2)
    singleton = [[0], [1]]
    paired = [[0, 1], [0, 1]]
    half = scale(Fraction(1, 2), i2)
    good = [z2, half, half, z2]
    cases = []
    for n in (2, 3, 5, 17):
        d = n * n + 1
        p, q = rational_pair(n)
        xp, xq = subtract(i2, p), subtract(i2, q)
        y = scale(Fraction(1, 2), subtract(add(xp, xq), scale(Fraction(2*n, d), i2)))
        span_dimension = verify_support_separator(
            [p, q], singleton, [p, q], {1: p, 2: q, 3: z2}, y)
        require_equal(span_dimension, 2, "permitted subspaces span the whole space")
        denominator, numerator, _ = verify_dual([p, q], singleton, [xp, xq], y)
        require_equal(denominator, 0, "zero energy denominator")
        if numerator <= 0:
            raise RuntimeError("Separating trace must be positive")

        # K^(-1/2) has a common square root scalar; it cancels rationally.
        g = scale(Fraction(1, d), outer([[n], [-1]]))
        j = subtract(i2, g)
        inverse_factor = add(g, scale(Fraction(1, n), j))
        ep = scale(Fraction(d, 2), multiply(multiply(inverse_factor, p), inverse_factor))
        eq = scale(Fraction(d, 2), multiply(multiply(inverse_factor, q), inverse_factor))
        normalized = [z2, ep, eq, z2]
        verify_joint_support([p, q], normalized)
        expected_ep = scale(Fraction(1, 2*d),
                            [[(n-1)**2, -(n*n-1)], [-(n*n-1), (n+1)**2]])
        require_equal(ep, expected_ep, "closed form of normalized effect")
        kernel_leak = Fraction((n-1)**2, 2*d)
        require_equal(ep[0][0], kernel_leak, "positive effect on kernel of P")
        rejected = expect_rejected(verify_kernel_resolution,
                                   [p, q], singleton, normalized, [p, q])

        energies = verify_kernel_resolution([p, q], paired, good, [i2, i2])
        delta = Fraction(2, d)
        verify_spectral_bound(energies, [i2, i2], delta)
        preparations = {1: xq, 2: xp}
        verify_primal([p, q], paired, good, 1/delta, preparations)
        verify_primal([p, q], paired, good, Fraction(d, 4), preparations)
        false_delta = expect_rejected(verify_spectral_bound,
                                      energies, [i2, i2], delta + Fraction(1, d))
        cases.append({
            "N": n,
            "singleton": {
                "permitted_support_span_dimension": span_dimension,
                "separator_Y": encoded(y), "trace_Y": str(numerator),
                "dual_denominator": str(denominator),
                "identity_resolution": "impossible by exact separator",
            },
            "normalization_attempt": {
                "effects": [encoded(ep), encoded(eq)], "kernel_leak": str(kernel_leak),
                "support_check_rejected": rejected,
            },
            "paired": {
                "effects_by_label": [encoded(e) for e in good],
                "delta": str(delta), "support_only_C0_bound": str(1/delta),
                "verified_sharp_C0": str(Fraction(d, 4)),
                "incorrect_larger_delta_rejected": false_delta,
            },
        })

    p, q = rational_pair(1)
    orthogonal = [z2, p, q, z2]
    energies = verify_kernel_resolution([p, q], singleton, orthogonal, [p, q])
    verify_spectral_bound(energies, [p, q], Fraction(1))
    verify_primal([p, q], singleton, orthogonal, Fraction(1), {1: p, 2: q})

    # All neighborhood sums may vanish in a frustration-free instance.
    empty_only = [i2, z2, z2, z2]
    energies = verify_kernel_resolution([p, p], [[], []], empty_only, [z2, z2])
    verify_spectral_bound(energies, [z2, z2], Fraction(1))
    verify_primal([p, p], [[], []], empty_only, Fraction(0), {0: subtract(i2, p)})

    # Two tensor copies use the same finite term collection and same constants.
    p, q = rational_pair(2)
    terms = [embed(p, 0, 2), embed(q, 0, 2), embed(p, 1, 2), embed(q, 1, 2)]
    neighborhoods = [[0, 1], [0, 1], [2, 3], [2, 3]]
    effects, preparations = [], {}
    for label in range(16):
        local_labels = [label & 3, (label >> 2) & 3]
        if all(local in (1, 2) for local in local_labels):
            effects.append(scale(Fraction(1, 4), identity(4)))
            states = [subtract(i2, q if local == 1 else p) for local in local_labels]
            preparations[label] = kronecker(states[0], states[1])
        else:
            effects.append(zero(4))
    energies = verify_kernel_resolution(terms, neighborhoods, effects, [identity(4)]*4)
    verify_spectral_bound(energies, [identity(4)]*4, Fraction(2, 5))
    verify_primal(terms, neighborhoods, effects, Fraction(5, 4), preparations)

    dependencies = ["check_qpcp_kernel_resolution.py", "check_qpcp_syndrome_sdp.py",
                    "check_qpcp_syndrome_support.py", "check_qpcp_rounding.py"]
    return {
        "status": "passed", "arithmetic": "exact rational",
        "source_sha256": {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                          for name in dependencies},
        "instances": cases,
        "orthogonal_boundary": {"delta": "1", "C0": "1"},
        "zero_neighborhood_boundary": {"C0": "0", "empty_fault_effect": "identity"},
        "two_copy_fixed_term_collection": {"N_in_term_matrix": 2, "copies": 2,
                                            "delta": "2/5", "C0": "5/4", "occurrence_R": 2},
        "scope": "Explicit certificate replays; the general cone alternative and uniform bound have analytic proofs.",
        "quantum_pcp_proved": False, "lean_checked": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "verified_N": [row["N"] for row in result["instances"]],
                      "normalization_support_failures": len(result["instances"]),
                      "positive_boundaries": ["orthogonal", "zero neighborhoods", "two tensor copies"],
                      "quantum_pcp_proved": False}, indent=2))


if __name__ == "__main__":
    main()
