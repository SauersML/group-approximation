#!/usr/bin/env sage
"""Direct octad-complement fusion and normalizer audit in natural M24."""

import json

from sage.all import libgap


def main():
    group = libgap.MathieuGroup(24)
    if int(group.Size()) != 244823040:
        raise AssertionError("MathieuGroup(24) order changed")

    # Wilson's canonical MOG octad for the standard degree-24 generators.
    octad = libgap.Set([24, 3, 6, 9, 23, 19, 15, 5])
    carrier = libgap.Stabilizer(group, octad, libgap.OnSets)
    if int(carrier.Size()) != 322560:
        raise AssertionError("canonical set is not an octad in this M24 model")

    translations = carrier.Socle()
    if int(translations.Size()) != 16 or not bool(translations.IsElementaryAbelian()):
        raise AssertionError("octad carrier lost its elementary abelian socle")
    complements = list(libgap.ComplementClassesRepresentatives(carrier, translations))
    if not complements:
        raise AssertionError("octad carrier returned no A8 complement")
    if any(int(complement.Size()) != 20160 for complement in complements):
        raise AssertionError("octad complement order changed")
    if any(not bool(complement.IsSimpleGroup()) for complement in complements):
        raise AssertionError("octad complement stopped being simple")

    natural_points = libgap.eval("[1..24]")
    orbit_lengths = [
        sorted(int(orbit.Length()) for orbit in complement.Orbits(natural_points))
        for complement in complements
    ]
    ambient_conjugacy = [
        [bool(group.IsConjugate(left, right)) for right in complements]
        for left in complements
    ]
    ambient_normalizer_orders = [
        int(group.Normalizer(complement).Size()) for complement in complements
    ]
    ambient_centralizer_orders = [
        int(group.Centralizer(complement).Size()) for complement in complements
    ]
    carrier_normalizer_orders = [
        int(carrier.Normalizer(complement).Size()) for complement in complements
    ]

    if orbit_lengths != [[1, 8, 15]] * len(complements):
        raise AssertionError(f"unexpected affine-complement orbit types: {orbit_lengths}")
    if any(order != 20160 for order in ambient_normalizer_orders):
        raise AssertionError("affine A8 complement is not self-normalizing in M24")
    if any(order != 1 for order in ambient_centralizer_orders):
        raise AssertionError("affine A8 complement acquired ambient centralizer")
    if any(order != 20160 for order in carrier_normalizer_orders):
        raise AssertionError("affine A8 complement is not self-normalizing in its carrier")
    if not all(all(row) for row in ambient_conjugacy):
        raise AssertionError("octad complement classes failed to fuse in M24")

    print(json.dumps({
        "ambient": "M24",
        "ambient_order": int(group.Size()),
        "canonical_octad": [int(point) for point in octad],
        "octad_carrier_order": int(carrier.Size()),
        "translation_socle_order": int(translations.Size()),
        "carrier_complement_classes": len(complements),
        "natural_orbit_lengths": orbit_lengths,
        "ambient_conjugacy_matrix": ambient_conjugacy,
        "ambient_normalizer_orders": ambient_normalizer_orders,
        "ambient_centralizer_orders": ambient_centralizer_orders,
        "carrier_normalizer_orders": carrier_normalizer_orders,
        "ambient_class_sizes": [
            int(group.Size()) // order for order in ambient_normalizer_orders
        ],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
