#!/usr/bin/env sage
"""Exact complement-class certificate for A8 subgroups of 2^4:A8."""

import json

from sage.all import GF, GL, Permutation, PermutationGroup, libgap, vector


def main():
    field = GF(2)
    points = [
        vector(field, [(index >> coordinate) & 1 for coordinate in range(4)])
        for index in range(16)
    ]
    position = {tuple(point): index + 1 for index, point in enumerate(points)}

    def permutation(action):
        return Permutation([position[tuple(action(point))] for point in points])

    generators = [
        permutation(lambda point, matrix=matrix: matrix * point)
        for matrix in GL(4, field).gens()
    ]
    basis = [
        vector(field, [1 if row == column else 0 for row in range(4)])
        for column in range(4)
    ]
    generators.extend(
        permutation(lambda point, shift=shift: point + shift)
        for shift in basis
    )

    affine = PermutationGroup(generators)._libgap_()
    translation = next(
        subgroup
        for subgroup in affine.NormalSubgroups()
        if int(subgroup.Size()) == 16 and bool(subgroup.IsElementaryAbelian())
    )
    complements = list(
        libgap.ComplementClassesRepresentatives(affine, translation)
    )
    moved_orbit_profiles = [
        sorted(len(list(orbit)) for orbit in complement.Orbits())
        for complement in complements
    ]

    assert int(affine.Size()) == 322560
    assert len(complements) == 1
    assert [int(complement.Size()) for complement in complements] == [20160]
    assert moved_orbit_profiles == [[15]]

    print(json.dumps({
        "affine_group_order": int(affine.Size()),
        "complement_class_count": len(complements),
        "complement_orders": [int(complement.Size()) for complement in complements],
        "moved_orbit_profiles": moved_orbit_profiles,
    }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()

