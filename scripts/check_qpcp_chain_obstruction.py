#!/usr/bin/env python3
"""Exact rational replay for the fixed-term spin-chain obstruction.

Finite matrix checks support, but do not replace, the all-size proof in
research/artifacts/qpcp-fixed-term-chain-2026-09-07.md.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from math import comb
from pathlib import Path

from check_qpcp_rounding import add, kronecker, multiply, outer, rank, require_equal, scale
from check_qpcp_syndrome_support import CertificateError, identity, require_psd, subtract, trace, zero
from check_qpcp_syndrome_sdp import encoded, expect_rejected
from check_qpcp_kernel_resolution import verify_range_projection, verify_spectral_bound


def tensor(matrices):
    result = [[Fraction(1)]]
    for matrix in matrices:
        result = kronecker(result, matrix)
    return result


def total(matrices, dimension):
    result = zero(dimension)
    for matrix in matrices:
        result = add(result, matrix)
    return result


def block(term, start, width, n):
    return tensor([identity(1 << start), term, identity(1 << (n-start-width))])


def chain_terms(n, same_boundary=False):
    if n < 2:
        raise CertificateError("At least two sites are required")
    p1 = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(1)]]
    p0 = subtract(identity(2), p1)
    singlet = scale(Fraction(1, 2), outer([[0], [1], [-1], [0]]))
    return ([block(p1, 0, 1, n)]
            + [block(singlet, i, 2, n) for i in range(n-1)]
            + [block(p1 if same_boundary else p0, n-1, 1, n)])


def symmetric_projection(r):
    return [[Fraction(1, comb(r, x.bit_count())) if x.bit_count() == y.bit_count()
             else Fraction(0) for y in range(1 << r)] for x in range(1 << r)]


def subset_kernel_projection(n, indices):
    selected = set(indices)
    components, first = [], 0
    for edge in range(1, n):
        if edge not in selected:
            components.append((first, edge-1))
            first = edge
    components.append((first, n-1))
    blocks = []
    for left, right in components:
        r = right-left+1
        pinned_zero = left == 0 and 0 in selected
        pinned_one = right == n-1 and n in selected
        if pinned_zero and pinned_one:
            return zero(1 << n)
        if pinned_zero or pinned_one:
            projection = zero(1 << r)
            index = 0 if pinned_zero else (1 << r)-1
            projection[index][index] = Fraction(1)
            blocks.append(projection)
        else:
            blocks.append(symmetric_projection(r))
    return tensor(blocks)


def product_trial(n):
    t = n-1
    norms = [(t-j)**2+j*j for j in range(n)]
    states = [scale(Fraction(1, norms[j]), outer([[t-j], [j]])) for j in range(n)]
    energy = sum((Fraction(t*t, 2*norms[j]*norms[j+1]) for j in range(n-1)), Fraction(0))
    if energy > Fraction(2, t):
        raise RuntimeError("Variational energy bound failed")
    for j, norm in enumerate(norms):
        require_equal(2*norm-t*t, (t-2*j)**2, "normalization lower bound identity")
    return states, tensor(states), energy


def verify_dual_slacks(energies, ranges, xs, y):
    if trace(y) <= 0:
        raise CertificateError("Separating trace is not positive")
    dimension = len(y)
    for a, (energy, projection, x) in enumerate(zip(energies, ranges, xs)):
        verify_range_projection(energy, projection)
        require_psd(x, f"positive kernel penalty {a}")
        require_equal(multiply(x, energy), zero(dimension), "zero dual energy denominator")
        # This stronger singleton inequality implies every nonempty-label slack.
        require_psd(subtract(x, y), f"singleton dual slack {a}")


def range_cover_certificate(terms, energies, ranges, rho):
    dimension = len(rho)
    if len(terms) != len(energies) or len(terms) != len(ranges):
        raise CertificateError("Expected one energy and range per fault label")
    if rank(total(terms, dimension)) != dimension:
        raise CertificateError("The empty fault set is feasible; frustration is required")
    require_psd(rho, "input density matrix")
    require_equal(trace(rho), Fraction(1), "input trace")
    for energy, projection in zip(energies, ranges):
        verify_range_projection(energy, projection)
    eta = 1-sum(trace(multiply(projection, rho)) for projection in ranges)
    if eta <= 0:
        raise CertificateError("No positive range-cover deficit")
    y0 = subtract(rho, total([multiply(multiply(p, rho), p) for p in ranges], dimension))
    epsilon = eta/(2*dimension)
    t = 2+8*dimension/eta
    y = subtract(y0, scale(epsilon, identity(dimension)))
    xs = [scale(t, subtract(identity(dimension), p)) for p in ranges]
    require_equal(trace(y), eta/2, "positive separating trace")
    verify_dual_slacks(energies, ranges, xs, y)
    return eta, epsilon, t, xs, y


def replay():
    subset_checks, dual_checks = [], []
    for n in (2, 3, 4, 5):
        dimension = 1 << n
        terms = chain_terms(n)
        for index, term in enumerate(terms):
            require_psd(term, f"term {index}")
            require_equal(multiply(term, term), term, "projector term")
        require_equal(rank(total(terms, dimension)), dimension, "frustration")
        require_equal(subset_kernel_projection(n, range(n+1)), zero(dimension), "full common kernel")

        # Every one-term deletion is feasible; positivity extends this to supersets.
        for removed in range(n+1):
            indices = [a for a in range(n+1) if a != removed]
            projection = subset_kernel_projection(n, indices)
            if rank(projection) == 0:
                raise RuntimeError("A singleton fault label unexpectedly became infeasible")
            require_equal(multiply(total([terms[a] for a in indices], dimension), projection),
                          zero(dimension), "one-term deletion kernel")

        l = min(3, n)
        delta = Fraction(1, 8*(l+1)**4)
        count = 0
        for size in range(l+1):
            for indices in combinations(range(n+1), size):
                energy = total([terms[a] for a in indices], dimension)
                kernel = subset_kernel_projection(n, indices)
                projection = subtract(identity(dimension), kernel)
                verify_range_projection(energy, projection)
                verify_spectral_bound([energy], [projection], delta)
                count += 1
        require_equal(count, sum(comb(n+1, size) for size in range(l+1)), "all tested subsets counted")
        states, rho, energy = product_trial(n)
        require_psd(rho, "product trial")
        require_equal(trace(rho), Fraction(1), "normalized product trial")
        require_equal(trace(multiply(total(terms, dimension), rho)), energy, "exact variational energy")
        require_equal(trace(multiply(terms[0], rho)), Fraction(0), "left endpoint exact")
        require_equal(trace(multiply(terms[-1], rho)), Fraction(0), "right endpoint exact")
        subset_checks.append({"n": n, "L": l, "all_subsets_up_to_L_checked": count,
                              "delta": str(delta), "trial_energy": str(energy),
                              "energy_upper_bound": str(Fraction(2, n-1)), "minimum_fault_cardinality": 1})

        if n <= 4:
            eta, epsilon, t, xs, y = range_cover_certificate(terms, terms, terms, rho)
            rejection = expect_rejected(verify_dual_slacks, terms, terms, xs, scale(2, identity(dimension)))
            row = {"n": n, "neighborhoods": "singleton terms; P_a=h_a",
                   "site_density_matrices": [encoded(state) for state in states],
                   "eta": str(eta), "epsilon": str(epsilon), "t": str(t),
                   "X_formula": "X_a=t(I-h_a)",
                   "Y_formula": "rho-sum_a h_a rho h_a-epsilon I",
                   "trace_Y": str(trace(y)), "dual_denominator": "0",
                   "all_singleton_slacks_checked": len(xs), "invalid_dual_rejected": rejection}
            if n == 2:
                row["dense_Y"] = encoded(y)
            dual_checks.append(row)

    # The positive-trace certificate requires an infeasible empty label.
    ff_terms = chain_terms(2, same_boundary=True)
    all_zero = zero(4)
    all_zero[0][0] = Fraction(1)
    ff_rejection = expect_rejected(range_cover_certificate, ff_terms, ff_terms, ff_terms, all_zero)
    spectral_rejection = expect_rejected(verify_spectral_bound,
                                          [ff_terms[0]], [ff_terms[0]], Fraction(2))

    thresholds = []
    for l, r in ((1, 1), (2, 1), (3, 2), (5, 4)):
        n = 1+32*r*(l+1)**4
        delta = Fraction(1, 8*(l+1)**4)
        energy_bound = Fraction(2, n-1)
        coverage_bound = r*energy_bound/delta
        require_equal(coverage_bound, Fraction(1, 2), "all-size scalar coverage bound")
        if not n > 1+16*r*(l+1)**4 or not n+1 > l:
            raise RuntimeError("Threshold hypotheses failed")
        thresholds.append({"L": l, "R": r, "n": n, "delta": str(delta),
                           "energy_upper_bound": str(energy_bound), "range_mass_upper_bound": "1/2",
                           "scope": "Scalar bound replay; all-size operator estimates use the analytic proof."})

    dependencies = ["check_qpcp_chain_obstruction.py", "check_qpcp_kernel_resolution.py",
                    "check_qpcp_syndrome_sdp.py", "check_qpcp_syndrome_support.py", "check_qpcp_rounding.py"]
    return {
        "status": "passed", "arithmetic": "exact rational",
        "source_sha256": {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                          for name in dependencies},
        "local_subset_replays": subset_checks, "explicit_dual_replays": dual_checks,
        "all_size_scalar_bounds": thresholds,
        "negative_controls": {"frustration_free_case_rejected": ff_rejection,
                              "false_spectral_bound_rejected": spectral_rejection},
        "quantum_pcp_proved": False, "constant_combinatorial_gap_proved_for_chain": False,
        "lean_checked": False, "wolfram_checked": False,
        "scope": "Exact finite matrix certificates plus scalar threshold checks; the artifact proves the all-size theorem.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "local_subsets_checked": sum(row["all_subsets_up_to_L_checked"] for row in result["local_subset_replays"]),
                      "explicit_dual_chains": [row["n"] for row in result["explicit_dual_replays"]],
                      "scalar_threshold_cases": len(result["all_size_scalar_bounds"]),
                      "quantum_pcp_proved": False}, indent=2))


if __name__ == "__main__":
    main()
