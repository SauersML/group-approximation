#!/usr/bin/env sage
"""Exact complement classes in the O8+(2) maximal carrier 2^6:A8."""

import json

from sage.all import GF, Matrix, Permutation, PermutationGroup, libgap, vector


def quotient_matrix(permutation):
    """A8 action on even F2^8 / <(1,...,1)> in the f1,...,f6 basis."""
    columns = []
    for index in range(1, 7):
        left, right = permutation[index - 1], permutation[7]
        coefficients = [0] * 7
        if left != 8:
            coefficients[left - 1] ^= 1
        if right != 8:
            coefficients[right - 1] ^= 1
        # f7 equals f1+...+f6 modulo the all-ones vector.
        if coefficients[6]:
            for position in range(6):
                coefficients[position] ^= 1
        columns.append(coefficients[:6])
    return Matrix(GF(2), 6, 6, lambda row, column: columns[column][row])


def main():
    field = GF(2)
    permutations = [
        (2, 3, 1, 4, 5, 6, 7, 8),
        (1, 3, 4, 5, 6, 7, 8, 2),
    ]
    matrices = [quotient_matrix(permutation) for permutation in permutations]
    points = [
        vector(field, [(index >> coordinate) & 1 for coordinate in range(6)])
        for index in range(64)
    ]
    position = {tuple(point): index + 1 for index, point in enumerate(points)}

    def affine_permutation(action):
        return Permutation([position[tuple(action(point))] for point in points])

    linear_generators = [
        affine_permutation(lambda point, matrix=matrix: matrix * point)
        for matrix in matrices
    ]
    basis = [
        vector(field, [1 if row == column else 0 for row in range(6)])
        for column in range(6)
    ]
    translation_generators = [
        affine_permutation(lambda point, shift=shift: point + shift)
        for shift in basis
    ]
    affine = PermutationGroup(linear_generators + translation_generators)._libgap_()
    translation = PermutationGroup(translation_generators)._libgap_()
    complement_representatives = list(
        libgap.ComplementClassesRepresentatives(affine, translation)
    )
    normalizer_orders = [
        int(affine.Normalizer(complement).Size())
        for complement in complement_representatives
    ]
    orbit_profiles = [
        sorted(int(len(orbit)) for orbit in complement.Orbits())
        for complement in complement_representatives
    ]

    if int(affine.Size()) != 64 * 20160:
        raise AssertionError("2^6:A8 carrier order changed")
    if int(translation.Size()) != 64:
        raise AssertionError("translation subgroup order changed")
    if any(int(complement.Size()) != 20160 for complement in complement_representatives):
        raise AssertionError("non-A8 complement returned")
    if len(complement_representatives) != 2:
        raise AssertionError("2^6:A8 complement-class count changed")
    if normalizer_orders != [20160, 20160]:
        raise AssertionError("2^6:A8 complement normalizers changed")
    if orbit_profiles != [[28, 35], [8, 56]]:
        raise AssertionError("2^6:A8 affine complement orbit profiles changed")

    print(json.dumps({
        "carrier": "2^6:A8 on the six-dimensional orthogonal A8 module",
        "carrier_order": int(affine.Size()),
        "complement_class_count": len(complement_representatives),
        "complement_orders": [
            int(complement.Size()) for complement in complement_representatives
        ],
        "normalizer_orders_in_carrier": normalizer_orders,
        "affine_orbit_profiles": orbit_profiles,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
