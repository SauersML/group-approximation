#!/usr/bin/env sage
"""Read the two official ATLAS degree-1100 HS actions and identify the S8 one."""

import json
import urllib.request

from sage.all import libgap


BASE = "https://brauer.maths.qmul.ac.uk/Atlas/spor/HS/gap/"


def atlas_permutation(filename):
    text = urllib.request.urlopen(BASE + filename, timeout=30).read().decode("ascii")
    expression = text.split(":=", 1)[1].strip()
    if expression.endswith(";"):
        expression = expression[:-1]
    return libgap.eval(expression)


def main():
    records = []
    for identifier in ("a", "b"):
        a = atlas_permutation(f"HSG1-p1100{identifier}B0.g1")
        b = atlas_permutation(f"HSG1-p1100{identifier}B0.g2")
        group = libgap.Group([a, b])
        stabilizer = group.Stabilizer(1)
        derived = stabilizer.DerivedSubgroup()
        is_a8 = libgap.IsomorphismGroups(derived, libgap.AlternatingGroup(8)) != libgap.fail
        orbits = sorted(
            list(stabilizer.Orbits(libgap.eval("[1..1100]"))),
            key=lambda orbit: int(len(orbit)),
        )
        orbit_sizes = [int(len(orbit)) for orbit in orbits]
        cells = []
        for orbit in orbits:
            point = int(orbit[0])
            transporter = group.RepresentativeAction(1, point)
            moved_stabilizer = stabilizer ** transporter
            moved_derived = derived ** transporter
            stabilizer_intersection = stabilizer.Intersection(moved_stabilizer)
            derived_intersection = derived.Intersection(moved_derived)
            generated = libgap.Group(
                list(derived.GeneratorsOfGroup()) + list(moved_derived.GeneratorsOfGroup())
            )
            cells.append({
                "subdegree": int(len(orbit)),
                "stabilizer_intersection_order": int(stabilizer_intersection.Size()),
                "derived_intersection_order": int(derived_intersection.Size()),
                "derived_intersection_structure": str(derived_intersection.StructureDescription()),
                "generated_by_two_derived_subgroups_order": int(generated.Size()),
            })
        records.append({
            "representation": identifier,
            "group_order": int(group.Size()),
            "stabilizer_order": int(stabilizer.Size()),
            "derived_order": int(derived.Size()),
            "derived_is_A8": bool(is_a8),
            "subdegrees": orbit_sizes,
            "intersection_orders": [int(stabilizer.Size()) // size for size in orbit_sizes],
            "cells": cells,
        })

    s8_records = [record for record in records if record["derived_is_A8"]]
    if len(s8_records) != 1:
        raise AssertionError("expected one ATLAS degree-1100 action with S8 stabilizer")
    if any(record["group_order"] != 44352000 for record in records):
        raise AssertionError("HS order calibration changed")
    s8 = s8_records[0]
    if s8["subdegrees"] != [1, 28, 105, 336, 630]:
        raise AssertionError("HS/S8 subdegrees changed")
    expected_cells = [
        (1, 40320, 20160, "A8", 20160),
        (28, 1440, 720, "S6", 44352000),
        (105, 384, 192, "(((C2 x C2 x C2) : (C2 x C2)) : C3) : C2", 44352000),
        (336, 120, 60, "A5", 44352000),
        (630, 64, 16, "C2 x D8", 44352000),
    ]
    actual_cells = [
        (
            cell["subdegree"],
            cell["stabilizer_intersection_order"],
            cell["derived_intersection_order"],
            cell["derived_intersection_structure"],
            cell["generated_by_two_derived_subgroups_order"],
        )
        for cell in s8["cells"]
    ]
    if actual_cells != expected_cells:
        raise AssertionError(f"HS/S8 double-coset data changed: {actual_cells}")
    print(json.dumps({
        "source": "official ATLAS HS degree-1100 GAP generators",
        "actions": records,
        "S8_action": s8_records[0]["representation"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
