"""Classify the generic residual primary boundary over ``QQ(t)``.

This MSI-only symbolic experiment reads the fixed natural-model templates,
chooses every orientation-reversing source eigenspace of projective
dimension one, parameterizes it over a rational function field, and groups
the six residual boundary images into target-stabilizer orbits.  It is a
generic-stratum theorem-discovery tool; exceptional parameter values still
require separate exact treatment.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from sage.all import QQ, PolynomialRing, QuadraticField, identity_matrix, matrix, vector


def parse(path: Path):
    result = {"SOURCE": [], "TARGET": [], "BOUNDARY": []}
    for line in path.read_text(encoding="utf-8").splitlines():
        kind, sign, entries = line.split()
        values = [int(value) for value in entries.split(",")]
        result[kind].append((int(sign), matrix(QQ, 3, 3, values)))
    return result


def proportional(left, right):
    return all(
        left[i] * right[j] == left[j] * right[i]
        for i in range(3)
        for j in range(i + 1, 3)
    )


def proportional_polynomial(left, right, polynomial):
    minors = [
        left[i] * right[j] - left[j] * right[i]
        for i in range(3)
        for j in range(i + 1, 3)
    ]
    numerators = [polynomial(value.numerator()) for value in minors if value]
    if not numerators:
        return polynomial.zero()
    common = numerators[0]
    for value in numerators[1:]:
        common = common.gcd(value)
    return common.monic()


def target_equivalent(left, right, target):
    return any(proportional(left * element, right) for _, element in target)


def target_bad(point, target):
    return any(
        sign == -1 and proportional(point * element, point)
        for sign, element in target
    )


def orbit_representatives(points, group):
    representatives = []
    for point in points:
        if not any(target_equivalent(point, representative, group)
                   for representative in representatives):
            representatives.append(point)
    return representatives


def normalized_strings(point):
    first = next(value for value in point if value)
    return [str(value / first) for value in point]


def residual_profile(point, target, boundary):
    field = point.base_ring()
    images = [point * element.change_ring(field) for _, element in boundary]
    bad = [target_bad(image, target) for image in images]
    classes = []
    for index, image in enumerate(images):
        if not bad[index]:
            continue
        if not any(target_equivalent(image, representative, target)
                   for representative in classes):
            classes.append(image)
    multiplicities = [
        sum(
            1
            for index, image in enumerate(images)
            if bad[index] and target_equivalent(image, representative, target)
        )
        for representative in classes
    ]
    return {
        "target_bad_boundary_terms": sum(bad),
        "target_orbit_multiplicities": multiplicities,
        "odd_target_orbit_count": sum(value % 2 for value in multiplicities),
    }


def generic_source_planes(source):
    planes = []
    keys = set()
    identity = identity_matrix(QQ, 3)
    for sign, element in source:
        if sign != -1:
            continue
        for eigenvalue in element.charpoly().roots(QQ, multiplicities=False):
            eigenspace = (element.transpose() - eigenvalue * identity).right_kernel()
            if eigenspace.dimension() != 2:
                continue
            key = tuple(eigenspace.basis_matrix().echelon_form().list())
            if key not in keys:
                keys.add(key)
                planes.append(eigenspace)
    return planes


def analyze(path: Path):
    templates = parse(path)
    source = templates["SOURCE"]
    target = templates["TARGET"]
    boundary = templates["BOUNDARY"]
    polynomial = PolynomialRing(QQ, "t")
    fraction = polynomial.fraction_field()
    t = fraction.gen()

    strata = []
    rational_exception_points = []
    for plane in generic_source_planes(source):
        basis = [vector(fraction, row) for row in plane.basis()]
        point = basis[0] + t * basis[1]
        images = [point * element.change_ring(fraction) for _, element in boundary]
        bad = [target_bad(image, target) for image in images]
        classes = []
        for index, image in enumerate(images):
            if not bad[index]:
                continue
            position = next(
                (position for position, representative in enumerate(classes)
                 if target_equivalent(image, representative, target)),
                None,
            )
            if position is None:
                classes.append(image)
        multiplicities = [
            sum(
                1
                for index, image in enumerate(images)
                if bad[index] and target_equivalent(image, representative, target)
            )
            for representative in classes
        ]
        exceptional_factors = set()
        exceptional_tests = []
        for sign, element in source:
            if sign != -1:
                continue
            obstruction = proportional_polynomial(
                point * element.change_ring(fraction), point, polynomial)
            exceptional_tests.append(obstruction)
        for image in images:
            for sign, element in target:
                if sign != -1:
                    continue
                obstruction = proportional_polynomial(
                    image * element.change_ring(fraction), image, polynomial)
                exceptional_tests.append(obstruction)
        for left_index, left in enumerate(images):
            for right in images[left_index + 1:]:
                for _, element in target:
                    obstruction = proportional_polynomial(
                        left * element.change_ring(fraction), right, polynomial)
                    exceptional_tests.append(obstruction)
        exceptional_polynomials = set()
        for obstruction in exceptional_tests:
            if obstruction.degree() <= 0:
                continue
            for factor, _ in obstruction.factor():
                exceptional_polynomials.add(factor.monic())
                exceptional_factors.add(str(factor.monic()))
        rational_basis = [vector(QQ, row) for row in plane.basis()]
        rational_exception_points.append(rational_basis[1])
        for factor in exceptional_polynomials:
            if factor.degree() == 1:
                root = -factor[0] / factor[1]
                rational_exception_points.append(
                    rational_basis[0] + root * rational_basis[1])
        strata.append({
            "plane_basis": [[str(value) for value in row] for row in plane.basis()],
            "target_bad_boundary_terms": sum(bad),
            "generic_target_orbit_multiplicities": multiplicities,
            "odd_target_orbit_count": sum(value % 2 for value in multiplicities),
            "finite_exceptional_factors": sorted(exceptional_factors),
            "infinite_parameter_is_exceptional": True,
        })

    rational_representatives = orbit_representatives(
        rational_exception_points, source)
    rational_exception_orbits = [
        {
            "representative": normalized_strings(point),
            **residual_profile(point, target, boundary),
        }
        for point in rational_representatives
    ]

    quadratic = QuadraticField(-1, "ii")
    quadratic_identity = identity_matrix(quadratic, 3)
    quadratic_lines = []
    for sign, element in source:
        if sign != -1:
            continue
        changed = element.change_ring(quadratic)
        for eigenvalue in changed.charpoly().roots(quadratic, multiplicities=False):
            eigenspace = (
                changed.transpose() - eigenvalue * quadratic_identity
            ).right_kernel()
            if eigenspace.dimension() == 1:
                quadratic_lines.append(vector(quadratic, eigenspace.basis()[0]))
    quadratic_representatives = orbit_representatives(quadratic_lines, source)
    quadratic_exception_orbits = []
    for point in quadratic_representatives:
        normalized = point / next(value for value in point if value)
        defined_over_QQ = all(value[1] == 0 for value in normalized)
        quadratic_exception_orbits.append({
            "representative": [str(value) for value in normalized],
            "defined_over_QQ": defined_over_QQ,
            **residual_profile(point, target, boundary),
        })
    return {
        "source_orientation_reversing_projective_planes": len(strata),
        "strata": strata,
        "rational_exception_orbits": rational_exception_orbits,
        "quadratic_negative_eigenline_orbits": quadratic_exception_orbits,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("template", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    result = analyze(args.template)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
