#!/usr/bin/env sage
"""Ambient O8+(2) fusion of the two A8 complements in 2^6:A8."""

import json

from sage.all import libgap


def main():
    group = libgap.PrimitiveGroup(135, 2)
    carrier = group.Stabilizer(1)
    translation_candidates = [
        subgroup
        for subgroup in carrier.NormalSubgroups()
        if int(subgroup.Size()) == 64 and bool(subgroup.IsElementaryAbelian())
    ]
    if len(translation_candidates) != 1:
        raise AssertionError("expected the unique normal 2^6 in the point stabilizer")
    translation = translation_candidates[0]
    complements = list(
        libgap.ComplementClassesRepresentatives(carrier, translation)
    )
    if len(complements) != 2:
        raise AssertionError("2^6:A8 complement-class count changed")

    records = []
    for complement in complements:
        ambient_normalizer = group.Normalizer(complement)
        containing_carriers = sum(
            1
            for point in range(1, 136)
            if bool(libgap.IsSubgroup(group.Stabilizer(point), complement))
        )
        records.append({
            "complement_order": int(complement.Size()),
            "carrier_normalizer_order": int(carrier.Normalizer(complement).Size()),
            "ambient_normalizer_order": int(ambient_normalizer.Size()),
            "ambient_class_size": int(group.Size()) // int(ambient_normalizer.Size()),
            "containing_carriers_in_this_triality_class": containing_carriers,
            "ambient_normalizer_structure": str(ambient_normalizer.StructureDescription()),
        })

    ambient_conjugate = bool(group.IsConjugate(complements[0], complements[1]))
    if ambient_conjugate:
        raise AssertionError("the two local complement classes fused in O8+(2)")
    if sorted(record["ambient_normalizer_order"] for record in records) != [20160, 40320]:
        raise AssertionError("ambient A8/S8 normalizer fork changed")
    if sorted(record["containing_carriers_in_this_triality_class"] for record in records) != [1, 2]:
        raise AssertionError("affine-carrier incidence count changed")
    print(json.dumps({
        "ambient": "O8+(2)",
        "ambient_order": int(group.Size()),
        "action_degree": 135,
        "point_stabilizer_order": int(carrier.Size()),
        "translation_order": int(translation.Size()),
        "local_complement_classes": len(complements),
        "local_classes_are_ambient_conjugate": ambient_conjugate,
        "classes": records,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
