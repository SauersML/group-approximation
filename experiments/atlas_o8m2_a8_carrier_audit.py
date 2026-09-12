#!/usr/bin/env sage
"""Exact A8 carrier and fusion audit in O8-(2)."""

import json

from sage.all import libgap


def main():
    group = libgap.PrimitiveGroup(119, 1)
    if int(group.Size()) != 197406720:
        raise AssertionError("PrimitiveGroup(119,1) is no longer O8-(2)")
    maximals = list(libgap.MaximalSubgroupClassReps(group))
    divisible = [subgroup for subgroup in maximals if int(subgroup.Size()) % 20160 == 0]
    if sorted(int(subgroup.Size()) for subgroup in divisible) != [120960, 1451520]:
        raise AssertionError("O8-(2) A8-divisible maximal carriers changed")

    sp6 = next(subgroup for subgroup in divisible if int(subgroup.Size()) == 1451520)
    direct = next(subgroup for subgroup in divisible if int(subgroup.Size()) == 120960)

    s8_candidates = [
        subgroup for subgroup in libgap.MaximalSubgroupClassReps(sp6)
        if int(subgroup.Size()) == 40320
        and int(subgroup.DerivedSubgroup().Size()) == 20160
    ]
    if len(s8_candidates) != 1:
        raise AssertionError("Sp6(2) orthogonal S8 carrier class changed")
    orthogonal = s8_candidates[0].DerivedSubgroup()

    direct_a8_candidates = [
        subgroup for subgroup in direct.NormalSubgroups()
        if int(subgroup.Size()) == 20160
        and bool(subgroup.IsSimpleGroup())
    ]
    if len(direct_a8_candidates) != 1:
        raise AssertionError("(3xA8):2 lost its unique normal A8")
    direct_a8 = direct_a8_candidates[0]

    fuse = bool(group.IsConjugate(orthogonal, direct_a8))
    if not fuse:
        raise AssertionError("orthogonal and direct-factor A8 classes stopped fusing")
    ambient_normalizer = group.Normalizer(direct_a8)
    ambient_centralizer = group.Centralizer(direct_a8)
    if int(ambient_normalizer.Size()) != 120960:
        raise AssertionError("ambient A8 normalizer changed")
    if int(ambient_centralizer.Size()) != 3:
        raise AssertionError("ambient A8 centralizer changed")
    if int(sp6.Normalizer(orthogonal).Size()) != 40320:
        raise AssertionError("orthogonal A8 lost its S8 normalizer inside Sp6(2)")

    ambient_class_size = int(group.Size()) // int(ambient_normalizer.Size())
    sp6_carriers = int(group.Size()) // int(sp6.Size())
    a8_per_sp6 = int(sp6.Size()) // int(sp6.Normalizer(orthogonal).Size())
    sp6_per_a8_numerator = sp6_carriers * a8_per_sp6
    if sp6_per_a8_numerator % ambient_class_size != 0:
        raise AssertionError("nonintegral Sp6/A8 incidence")
    sp6_per_a8 = sp6_per_a8_numerator // ambient_class_size
    if (ambient_class_size, sp6_carriers, a8_per_sp6, sp6_per_a8) != (1632, 136, 36, 3):
        raise AssertionError("O8-(2) A8 carrier incidence changed")

    print(json.dumps({
        "ambient": "O8-(2)",
        "ambient_order": int(group.Size()),
        "A8_divisible_maximal_carrier_orders": sorted(
            int(subgroup.Size()) for subgroup in divisible
        ),
        "orthogonal_and_direct_factor_A8_fuse": fuse,
        "A8_ambient_conjugacy_classes": 1,
        "A8_ambient_normalizer": "(3xA8):2",
        "A8_ambient_normalizer_order": int(ambient_normalizer.Size()),
        "A8_ambient_centralizer_order": int(ambient_centralizer.Size()),
        "A8_ambient_class_size": ambient_class_size,
        "Sp6_carriers": sp6_carriers,
        "A8_per_Sp6_carrier": a8_per_sp6,
        "Sp6_carriers_per_A8": sp6_per_a8,
        "relative_graph_parity_absorbed_by_ambient_normalizer": True,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
