#!/usr/bin/env sage
"""Fusion of affine A8 complements across the three O8+(2) triality carriers."""

import json

from sage.all import libgap


def main():
    group = libgap.PrimitiveGroup(135, 2)
    maximal_representatives = list(libgap.MaximalSubgroupClassReps(group))
    affine_carriers = [
        subgroup for subgroup in maximal_representatives
        if int(subgroup.Size()) == 1290240
    ]
    if len(affine_carriers) != 3:
        raise AssertionError(f"expected three 2^6:A8 classes, got {len(affine_carriers)}")

    complements = []
    labels = []
    for carrier_index, carrier in enumerate(affine_carriers, start=1):
        translations = [
            subgroup for subgroup in carrier.NormalSubgroups()
            if int(subgroup.Size()) == 64 and bool(subgroup.IsElementaryAbelian())
        ]
        if len(translations) != 1:
            raise AssertionError("affine carrier has no unique normal 2^6")
        local = list(libgap.ComplementClassesRepresentatives(carrier, translations[0]))
        if len(local) != 2:
            raise AssertionError("affine carrier complement count changed")
        for local_index, complement in enumerate(local, start=1):
            complements.append(complement)
            labels.append([carrier_index, local_index])

    conjugacy_matrix = [
        [bool(group.IsConjugate(left, right)) for right in complements]
        for left in complements
    ]
    ambient_normalizer_orders = [
        int(group.Normalizer(complement).Size()) for complement in complements
    ]

    def fusion_label(subgroup):
        matches = [
            index for index, complement in enumerate(complements)
            if bool(group.IsConjugate(subgroup, complement))
        ]
        if len(matches) != 1:
            raise AssertionError(f"carrier A8 has {len(matches)} affine fusion matches")
        return labels[matches[0]]

    orthogonal_carrier_fusions = []
    for carrier_index, carrier in enumerate(
        [subgroup for subgroup in maximal_representatives if int(subgroup.Size()) == 1451520],
        start=1,
    ):
        s8_candidates = [
            subgroup for subgroup in libgap.MaximalSubgroupClassReps(carrier)
            if int(subgroup.Size()) == 40320
            and int(subgroup.DerivedSubgroup().Size()) == 20160
        ]
        if len(s8_candidates) != 1:
            raise AssertionError("S6(2) carrier orthogonal S8 class changed")
        orthogonal_carrier_fusions.append({
            "carrier": carrier_index,
            "affine_fusion_label": fusion_label(s8_candidates[0].DerivedSubgroup()),
        })

    natural_carrier_fusions = []
    for carrier_index, carrier in enumerate(
        [subgroup for subgroup in maximal_representatives if int(subgroup.Size()) == 181440],
        start=1,
    ):
        a8_candidates = [
            subgroup for subgroup in libgap.MaximalSubgroupClassReps(carrier)
            if int(subgroup.Size()) == 20160
        ]
        if len(a8_candidates) != 1:
            raise AssertionError("A9 carrier natural A8 class changed")
        natural_carrier_fusions.append({
            "carrier": carrier_index,
            "affine_fusion_label": fusion_label(a8_candidates[0]),
        })
    # Connected components of the exact conjugacy equivalence relation.
    classes = []
    unused = set(range(len(complements)))
    while unused:
        seed = min(unused)
        component = {index for index in unused if conjugacy_matrix[seed][index]}
        classes.append(sorted(component))
        unused -= component
    label_to_index = {tuple(label): index for index, label in enumerate(labels)}
    if classes != [[0], [1], [2], [3], [4], [5]]:
        raise AssertionError("affine complement classes fused unexpectedly in O8+(2)")
    if sorted(ambient_normalizer_orders) != [20160] * 3 + [40320] * 3:
        raise AssertionError("triality A8/S8 normalizer multiplicities changed")
    natural_labels = [tuple(row["affine_fusion_label"]) for row in natural_carrier_fusions]
    orthogonal_labels = [
        tuple(row["affine_fusion_label"]) for row in orthogonal_carrier_fusions
    ]
    if len(set(natural_labels + orthogonal_labels)) != 6:
        raise AssertionError("natural and orthogonal carriers do not cover six A8 classes")
    if any(ambient_normalizer_orders[label_to_index[label]] != 20160 for label in natural_labels):
        raise AssertionError("natural A9 class acquired an unexpected ambient normalizer")
    if any(ambient_normalizer_orders[label_to_index[label]] != 40320 for label in orthogonal_labels):
        raise AssertionError("orthogonal S6 class lost its ambient S8 normalizer")

    print(json.dumps({
        "ambient": "O8+(2)",
        "affine_triality_carriers": len(affine_carriers),
        "labels_as_carrier_local_class": labels,
        "ambient_normalizer_orders": ambient_normalizer_orders,
        "ambient_conjugacy_matrix": conjugacy_matrix,
        "ambient_fusion_classes": [
            [labels[index] for index in component] for component in classes
        ],
        "orthogonal_S6_carrier_fusions": orthogonal_carrier_fusions,
        "natural_A9_carrier_fusions": natural_carrier_fusions,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
