#!/usr/bin/env sage
"""Normalizer double-coset and Sp6-carrier cells for A8 in O8-(2)."""

import json

from sage.all import libgap


def main():
    group = libgap.PrimitiveGroup(1632, 1)
    if int(group.Size()) != 197406720:
        raise AssertionError("PrimitiveGroup(1632,1) is no longer O8-(2)")
    normalizer = group.Stabilizer(1)
    if int(normalizer.Size()) != 120960:
        raise AssertionError("degree-1632 point stabilizer is not (3xA8):2")
    a8_candidates = [
        subgroup for subgroup in normalizer.NormalSubgroups()
        if int(subgroup.Size()) == 20160 and bool(subgroup.IsSimpleGroup())
    ]
    if len(a8_candidates) != 1:
        raise AssertionError("point stabilizer lost its unique normal A8")
    chart = a8_candidates[0]

    maximals = list(libgap.MaximalSubgroupClassReps(group))
    sp6_candidates = [subgroup for subgroup in maximals if int(subgroup.Size()) == 1451520]
    if len(sp6_candidates) != 1:
        raise AssertionError("O8-(2) Sp6(2) maximal class changed")
    sp6 = sp6_candidates[0]

    analyzer = libgap.eval(r"""
function(G,N,A,S)
  local domain, orbits, carrierClass, throughA, records, orbit, point, g,
        Ng, B, common, generated;
  domain := [1..LargestMovedPoint(G)];
  orbits := ShallowCopy(Orbits(N,domain,OnPoints));
  Sort(orbits,function(left,right) return Length(left)<Length(right); end);
  carrierClass := AsList(ConjugacyClassSubgroups(G,S));
  throughA := Filtered(carrierClass,carrier->IsSubgroup(carrier,A));
  records := [];
  for orbit in orbits do
    point := orbit[1];
    g := RepresentativeAction(G,1,point,OnPoints);
    Ng := N^g;
    B := A^g;
    common := Number(throughA,carrier->IsSubgroup(carrier,B));
    generated := Group(Concatenation(GeneratorsOfGroup(A),GeneratorsOfGroup(B)));
    Add(records,[Length(orbit),Size(Intersection(N,Ng)),
      Size(Intersection(A,B)),StructureDescription(Intersection(A,B)),
      Size(generated),common,point,g]);
  od;
  return [Length(carrierClass),Length(throughA),records];
end
""")
    result = analyzer(group, normalizer, chart, sp6)
    records = []
    for row in result[2]:
        records.append({
            "subdegree": int(row[0]),
            "normalizer_intersection_order": int(row[1]),
            "A8_intersection_order": int(row[2]),
            "A8_intersection_structure": str(row[3]),
            "generated_subgroup_order": int(row[4]),
            "common_Sp6_carriers": int(row[5]),
            "representative_point": int(row[6]),
            "representative_transporter": str(row[7]),
        })

    if sum(record["subdegree"] for record in records) != 1632:
        raise AssertionError("subdegrees do not sum to 1632")
    if int(result[0]) != 136 or int(result[1]) != 3:
        raise AssertionError("Sp6 carrier incidence changed")
    shared = sum(
        record["subdegree"] for record in records
        if record["common_Sp6_carriers"] > 0
    )
    if shared < 106:
        raise AssertionError("three 36-point Sp6 blocks lost expected neighbors")

    print(json.dumps({
        "ambient": "O8-(2)",
        "ambient_order": int(group.Size()),
        "A8_class_size": 1632,
        "A8_normalizer_order": int(normalizer.Size()),
        "Sp6_carriers": int(result[0]),
        "Sp6_carriers_through_fixed_A8": int(result[1]),
        "normalizer_double_coset_cells": len(records),
        "subdegrees": [record["subdegree"] for record in records],
        "points_in_cells_sharing_Sp6_with_fixed_A8": shared,
        "cells": records,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
