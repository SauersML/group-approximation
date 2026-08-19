"""Exact rank-one checks for the nonlinear discriminant repair formula.

For a primitive column ``a=(p,q)^T``, the map ``A:x |-> a*x`` has

    L = Z*a,                 K = Z*(-q,p),
    D_K = K^#/K ~= Z/(p^2+q^2).

The ambient integer lattice is the discriminant gluing of ``L`` and ``K``.
This script computes that gluing exactly, verifies on a rational grid that

    dist(t*a, Z^2)^2
      = min_c(dist(t*a, gamma(c))^2 + rho_K(c)^2),

and computes the exact optimal nonlinear repair constant

    sup_t dist(t,Z) / dist(t*a,Z^2).

The calculation is intentionally small and exact.  It is a regression test
for the general theorem in
``notes/TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md``,
not a numerical estimate for the large SL(3,Z) charts.
"""

import argparse
import json

from sage.all import QQ, gcd


def centered_residue(value, modulus):
    residue = int(value) % int(modulus)
    return min(residue, int(modulus) - residue)


def gluing_map(p, q):
    """Return the exact map from the K discriminant index to the L index."""
    norm_squared = p * p + q * q
    result = {}
    radius = 0
    while len(result) < norm_squared:
        radius += 1
        for first in range(-radius, radius + 1):
            for second in range(-radius, radius + 1):
                cycle_index = (-q * first + p * second) % norm_squared
                range_index = (p * first + q * second) % norm_squared
                old = result.get(cycle_index)
                if old is not None and old != range_index:
                    raise AssertionError("discriminant gluing is not a function")
                result[cycle_index] = range_index
        if radius > norm_squared:
            raise AssertionError("failed to enumerate the discriminant gluing")
    if len(set(result.values())) != norm_squared:
        raise AssertionError("discriminant gluing is not bijective")
    return result


def direct_defect_squared(p, q, parameter):
    first = p * parameter
    second = q * parameter
    return min(
        (first - first.floor()) ** 2 + (second - second.floor()) ** 2,
        (first - first.floor()) ** 2 + (second - second.ceil()) ** 2,
        (first - first.ceil()) ** 2 + (second - second.floor()) ** 2,
        (first - first.ceil()) ** 2 + (second - second.ceil()) ** 2,
    )


def distance_to_shifted_integer_squared(parameter, numerator, denominator):
    shifted = parameter - QQ(numerator) / denominator
    floor_value = shifted.floor()
    return min((shifted - floor_value) ** 2,
               (shifted - floor_value - 1) ** 2)


def discriminant_defect_squared(p, q, gluing, parameter):
    norm_squared = p * p + q * q
    values = []
    for cycle_index, range_index in gluing.items():
        cycle_radius = centered_residue(cycle_index, norm_squared)
        values.append(
            norm_squared * distance_to_shifted_integer_squared(
                parameter, range_index, norm_squared)
            + QQ(cycle_radius * cycle_radius) / norm_squared
        )
    return min(values)


def envelope_parabolas(p, q, gluing):
    norm_squared = p * p + q * q
    result = []
    for cycle_index, range_index in gluing.items():
        cycle_radius = centered_residue(cycle_index, norm_squared)
        residual = QQ(cycle_radius * cycle_radius) / norm_squared
        for shift in (-1, 0, 1):
            center = QQ(range_index) / norm_squared + shift
            result.append((center, residual, cycle_index, range_index))
    return result


def parabola_value(norm_squared, parabola, parameter):
    center, residual, _cycle_index, _range_index = parabola
    return norm_squared * (parameter - center) ** 2 + residual


def exact_repair_constant_squared(p, q, gluing):
    """Maximize the lower envelope ratio exactly on t in [0,1/2]."""
    norm_squared = p * p + q * q
    parabolas = envelope_parabolas(p, q, gluing)
    breakpoints = {QQ(0), QQ(1) / 2}
    for left_index, left in enumerate(parabolas):
        left_center, left_residual, _left_cycle, _left_range = left
        for right in parabolas[left_index + 1:]:
            right_center, right_residual, _right_cycle, _right_range = right
            coefficient = 2 * norm_squared * (right_center - left_center)
            if coefficient == 0:
                continue
            constant = (
                norm_squared * (right_center * right_center
                                - left_center * left_center)
                + left_residual - right_residual
            )
            crossing = constant / coefficient
            if 0 <= crossing <= QQ(1) / 2:
                breakpoints.add(crossing)

    ordered = sorted(breakpoints)
    candidates = {QQ(0), QQ(1) / 2}
    active_intervals = []
    for left, right in zip(ordered, ordered[1:]):
        if left == right:
            continue
        midpoint = (left + right) / 2
        values = [parabola_value(norm_squared, item, midpoint)
                  for item in parabolas]
        active = parabolas[values.index(min(values))]
        active_intervals.append((left, right, active))
        center, residual, _cycle_index, _range_index = active
        if center != 0:
            stationary = center + residual / (norm_squared * center)
            if left <= stationary <= right:
                candidates.add(stationary)
        candidates.add(left)
        candidates.add(right)

    best = QQ(1) / norm_squared
    best_parameter = QQ(0)
    for parameter in candidates:
        denominator = min(parabola_value(norm_squared, item, parameter)
                          for item in parabolas)
        value = (QQ(1) / norm_squared if denominator == 0
                 else parameter * parameter / denominator)
        if value > best:
            best = value
            best_parameter = parameter

    direct = direct_defect_squared(p, q, best_parameter)
    if best_parameter != 0 and best != best_parameter ** 2 / direct:
        raise AssertionError("exact optimizer disagrees with direct distance")
    return best, best_parameter, len(active_intervals)


def theta_squared(p, q, gluing):
    norm_squared = p * p + q * q
    best = QQ(1)
    best_class = 0
    for cycle_index, range_index in gluing.items():
        if cycle_index == 0:
            continue
        cycle_radius = centered_residue(cycle_index, norm_squared)
        range_radius = centered_residue(range_index, norm_squared)
        value = 1 + QQ(range_radius * range_radius) / (
            cycle_radius * cycle_radius)
        if value > best:
            best = value
            best_class = cycle_index
    return best, best_class


def analyze(p, q, grid_denominator):
    if gcd(p, q) != 1:
        raise ValueError("the rank-one column must be primitive")
    gluing = gluing_map(p, q)
    maximum_identity_error = QQ(0)
    for numerator in range(grid_denominator + 1):
        parameter = QQ(numerator) / grid_denominator
        direct = direct_defect_squared(p, q, parameter)
        paired = discriminant_defect_squared(p, q, gluing, parameter)
        maximum_identity_error = max(maximum_identity_error,
                                     abs(direct - paired))
    if maximum_identity_error != 0:
        raise AssertionError("paired discriminant distance identity failed")

    repair_squared, parameter, interval_count = exact_repair_constant_squared(
        p, q, gluing)
    carry_squared, carry_class = theta_squared(p, q, gluing)
    norm_squared = p * p + q * q
    return {
        "column": [int(p), int(q)],
        "norm_squared": int(norm_squared),
        "discriminant_order": int(norm_squared),
        "grid_denominator": int(grid_denominator),
        "grid_identity_exact": True,
        "grid_maximum_squared_error": str(maximum_identity_error),
        "gluing_cycle_to_range": {
            str(index): int(gluing[index]) for index in sorted(gluing)
        },
        "theta_squared": str(carry_squared),
        "theta_witness_cycle_class": int(carry_class),
        "optimal_repair_constant_squared": str(repair_squared),
        "optimal_parameter": str(parameter),
        "lower_envelope_interval_count": int(interval_count),
        "sharp_multiplicative_upper_bound_squared": str(
            carry_squared / norm_squared),
        "sharp_bound_is_exact": bool(
            repair_squared == carry_squared / norm_squared),
        "strictly_better_than_sharp_bound": bool(
            repair_squared < carry_squared / norm_squared),
    }


def build_result(grid_denominator):
    examples = [(1, 1), (1, 2), (2, 3), (2, 5), (3, 5)]
    return {
        "formula": "exact rank-one discriminant-envelope repair",
        "examples": [analyze(p, q, grid_denominator)
                     for p, q in examples],
    }


def verify(path):
    with open(path, "r", encoding="utf-8") as stream:
        expected = json.load(stream)
    denominators = {
        int(item["grid_denominator"]) for item in expected["examples"]
    }
    if len(denominators) != 1:
        raise AssertionError("stored examples use inconsistent grids")
    actual = build_result(denominators.pop())
    if actual != expected:
        raise AssertionError("stored exact-repair results do not verify")
    return {
        "valid": True,
        "examples": int(len(actual["examples"])),
        "exact_grid_identities": int(sum(
            int(item["grid_denominator"]) + 1
            for item in actual["examples"]
        )),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid-denominator", type=int, default=211)
    parser.add_argument("--verify")
    args = parser.parse_args()
    if args.verify:
        print(json.dumps(verify(args.verify), sort_keys=True))
        return
    if args.grid_denominator < 2:
        parser.error("--grid-denominator must be at least two")
    result = build_result(args.grid_denominator)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
