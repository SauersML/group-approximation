#!/usr/bin/env sage
"""Exact anti-flag orbit geometry for the unique A8 class in natural M24."""

import json

from sage.all import libgap


def main():
    group = libgap.MathieuGroup(24)
    if int(group.Size()) != 244823040:
        raise AssertionError("MathieuGroup(24) order changed")
    octad = libgap.Set([24, 3, 6, 9, 23, 19, 15, 5])
    point = 1
    if bool(point in octad):
        raise AssertionError("base point lies in canonical octad")
    carrier = libgap.Stabilizer(group, octad, libgap.OnSets)
    chart = carrier.Stabilizer(point)
    if int(carrier.Size()) != 322560 or int(chart.Size()) != 20160:
        raise AssertionError("canonical anti-flag stabilizer orders changed")

    analyzer = libgap.eval(r"""
function(G,A,O,p)
  local points, octads, antiflags, act, orbits, records, orbit, pair, q, C;
  points := [1..24];
  octads := Orbit(G,O,OnSets);
  antiflags := Concatenation(List(octads,
    C -> List(Difference(points,C),q -> [q,C])));
  act := function(pair,g)
    return [pair[1]^g,OnSets(pair[2],g)];
  end;
  orbits := OrbitsDomain(A,antiflags,act);
  records := [];
  for orbit in orbits do
    pair := orbit[1];
    q := pair[1];
    C := pair[2];
    Add(records,[Length(orbit),q,Size(Intersection(O,C)),p in C,
      q in O,O=C,C]);
  od;
  Sort(records,function(left,right)
    if left[5] <> right[5] then return left[5] < right[5]; fi;
    if left[1] <> right[1] then return left[1] < right[1]; fi;
    if left[3] <> right[3] then return left[3] < right[3]; fi;
    return left[2] < right[2];
  end);
  return [Length(octads),Length(antiflags),records];
end
""")
    result = analyzer(group, chart, octad, point)
    records = []
    for row in result[2]:
        target_point = int(row[1])
        target_in_octad = bool(row[4])
        same_octad = bool(row[5])
        if target_point == point:
            fiber = "fixed"
            absorbed = "same_fixed_point_M23"
        elif target_in_octad:
            fiber = "octad"
            absorbed = None
        else:
            fiber = "nonzero_affine"
            absorbed = "same_octad_affine" if same_octad else None
        records.append({
            "subdegree": int(row[0]),
            "chart_intersection_order": 20160 // int(row[0]),
            "target_fixed_point": target_point,
            "octad_intersection": int(row[2]),
            "base_point_in_target_octad": bool(row[3]),
            "target_point_in_base_octad": target_in_octad,
            "same_octad": same_octad,
            "fiber": fiber,
            "absorbed_reason": absorbed,
            "generates_M24": absorbed is None,
            "target_octad": [int(value) for value in row[6]],
        })

    if int(result[0]) != 759 or int(result[1]) != 12144:
        raise AssertionError("M24 octad/anti-flag counts changed")
    if sum(record["subdegree"] for record in records) != 12144:
        raise AssertionError("anti-flag orbit sizes do not sum to 12144")
    fiber_totals = {
        "fixed": sum(
            record["subdegree"] for record in records
            if record["target_fixed_point"] == point
        ),
        "octad": sum(
            record["subdegree"] for record in records
            if record["target_point_in_base_octad"]
        ),
        "nonzero_affine": sum(
            record["subdegree"] for record in records
            if record["target_fixed_point"] != point
            and not record["target_point_in_base_octad"]
        ),
    }
    if fiber_totals != {"fixed": 506, "octad": 4048, "nonzero_affine": 7590}:
        raise AssertionError(f"anti-flag fiber totals changed: {fiber_totals}")
    signatures = sorted(
        (
            record["fiber"], record["subdegree"], record["octad_intersection"],
            record["base_point_in_target_octad"], record["same_octad"],
        )
        for record in records
    )
    expected_signatures = sorted([
        ("fixed", 1, 8, False, True),
        ("fixed", 15, 0, False, False),
        ("fixed", 210, 4, False, False),
        ("fixed", 280, 2, False, False),
        ("octad", 120, 0, False, False),
        ("octad", 120, 0, True, False),
        ("octad", 280, 4, True, False),
        ("octad", 840, 4, False, False),
        ("octad", 1008, 2, True, False),
        ("octad", 1680, 2, False, False),
        ("nonzero_affine", 15, 8, False, True),
        ("nonzero_affine", 105, 0, False, False),
        ("nonzero_affine", 120, 0, True, False),
        ("nonzero_affine", 630, 4, False, False),
        ("nonzero_affine", 840, 4, True, False),
        ("nonzero_affine", 1680, 2, True, False),
        ("nonzero_affine", 1680, 4, False, False),
        ("nonzero_affine", 2520, 2, False, False),
    ])
    if signatures != expected_signatures:
        raise AssertionError(f"M24 anti-flag cell signatures changed: {signatures}")
    generating = [record for record in records if record["generates_M24"]]
    if len(generating) != 13 or sum(record["subdegree"] for record in generating) != 11623:
        raise AssertionError("M24 generating anti-flag cell count changed")

    print(json.dumps({
        "ambient": "M24",
        "base_point": point,
        "base_octad": [int(value) for value in octad],
        "octads": int(result[0]),
        "antiflags": int(result[1]),
        "A8_orbits_on_antiflags": len(records),
        "fiber_totals": fiber_totals,
        "generating_cells": len(generating),
        "generating_points": sum(record["subdegree"] for record in generating),
        "cells": records,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
