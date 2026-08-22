#!/usr/bin/env sage
"""Exact local packet-fan escape counts for the subfield A8 < GL(4,4)."""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sage.all import GF, GL, Matrix, libgap

from atlas_a4_19243_component_localization import H6_LABELS, H18_LABELS, order


def lifted(value, field):
    return Matrix(field, [[int(entry) for entry in row] for row in value])


def main():
    field = GF(4, "z")
    ambient = GL(4, field)
    components = []
    for name, labels in (("H6", H6_LABELS), ("H18", H18_LABELS)):
        involutions = [lifted(value, field) for value in labels if order(value) == 2]
        threes = [lifted(value, field) for value in labels if order(value) == 3]
        components.append((name, involutions, threes))

    fan_scanner = libgap.eval(r"""
function(G, representative, fans)
  local class, out, fan, count, inBase, x, good, a, overF2, row, entry;
  class := ConjugacyClass(G, representative);
  out := [];
  for fan in fans do
    count := 0;
    inBase := 0;
    for x in class do
      good := true;
      for a in fan do
        if (x*a)^3 <> One(G) then good := false; break; fi;
      od;
      if good then
        count := count + 1;
        overF2 := true;
        for row in x do
          for entry in row do
            if entry^2 <> entry then overF2 := false; break; fi;
          od;
          if not overF2 then break; fi;
        od;
        if overF2 then inBase := inBase + 1; fi;
      fi;
    od;
    Add(out, [Size(class), count, inBase]);
  od;
  return out;
end
""")

    involution = components[0][1][0]
    fans = libgap([[matrix._libgap_() for matrix in threes]
                   for _name, _involutions, threes in components])
    fan_result = fan_scanner(ambient, involution._libgap_(), fans)

    h6_involutions = components[0][1]
    h6_threes = components[0][2]
    products = [h6_involutions[0] * h6_involutions[1],
                h6_involutions[1] * h6_involutions[0]]
    assert set(map(str, products)) == set(map(str, h6_threes))
    pair_scanner = libgap.eval(r"""
function(G, representative, baseInvolutions, baseThrees)
  local class, candidates, x, good, a, ordered, inBase, y, mappedThrees,
        b, overF2, z, row, entry;
  class := ConjugacyClass(G, representative);
  candidates := [];
  for x in class do
    good := true;
    for a in baseThrees do
      if (x*a)^3 <> One(G) then good := false; break; fi;
    od;
    if good then Add(candidates, x); fi;
  od;
  ordered := 0;
  inBase := 0;
  for x in candidates do
    for y in candidates do
      if x = y or (x*y)^3 <> One(G) then continue; fi;
      mappedThrees := [x*y, y*x];
      good := true;
      for b in baseInvolutions do
        for a in mappedThrees do
          if (b*a)^3 <> One(G) then good := false; break; fi;
        od;
        if not good then break; fi;
      od;
      if good then
        ordered := ordered + 1;
        overF2 := true;
        for z in [x,y] do
          for row in z do
            for entry in row do
              if entry^2 <> entry then overF2 := false; break; fi;
            od;
            if not overF2 then break; fi;
          od;
          if not overF2 then break; fi;
        od;
        if overF2 then inBase := inBase + 1; fi;
      fi;
    od;
  od;
  return [Length(candidates), ordered, inBase];
end
""")
    pair_result = pair_scanner(
        ambient,
        involution._libgap_(),
        libgap([matrix._libgap_() for matrix in h6_involutions]),
        libgap([matrix._libgap_() for matrix in h6_threes]),
    )

    fan_counts = [[int(entry) for entry in row] for row in fan_result]
    pair_counts = [int(entry) for entry in pair_result]
    assert fan_counts == [[5355, 336, 18], [5355, 150, 18]]
    assert pair_counts == [336, 1262, 24]
    print(json.dumps({
        "ambient": "GL(4,4)",
        "subfield_chart": "GL(4,2)",
        "involution_class_size": 5355,
        "fan_columns": ["ambient_candidates", "subfield_candidates"],
        "H6_fan": [336, 18],
        "H18_fan": [150, 18],
        "H6_ordered_rectangle_pairs": 1262,
        "H6_ordered_rectangle_pairs_over_F2": 24,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

