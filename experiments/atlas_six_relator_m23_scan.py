#!/usr/bin/env sage
"""Exact six-relator double-coset screen in the maximal A8 class of M23."""

import json
import os

import numpy as np
from sage.all import GF, GL, libgap

from atlas_two_chart_search import gf2_inv


RELATOR_ORDER = ("s_0", "s_11", "s_30", "s_44", "s_55", "c_19243")


def atlas_m23_and_a8():
    # Official ATLAS M23G1-p23B0 generators and M23G1-max4W1 program.
    a = libgap.eval("(1,2)(3,4)(7,8)(9,10)(13,14)(15,16)(19,20)(21,22)")
    b = libgap.eval(
        "(1,16,11,3)(2,9,21,12)(4,5,8,23)(6,22,14,18)(13,20)(15,17)"
    )
    group = libgap.Group([a, b])
    r3 = a * b
    r4 = r3 * r3
    r5 = b * r4
    r3 = r4 * r4
    r6 = r3 * a
    r4 = r5 ** -1
    r3 = r4 * a
    h1 = r3 * r5
    r4 = r6 ** -1
    r3 = r4 * b
    h2 = r3 * r6
    chart = libgap.Group([h1, h2])
    if int(group.Size()) != 10200960 or int(chart.Size()) != 20160:
        raise AssertionError("ATLAS M23/maximal-A8 construction changed")
    if int(group.Normalizer(chart).Size()) != 20160:
        raise AssertionError("maximal A8 is not self-normalizing")
    return group, chart


def load_words():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-six-relator-relative-pieces.json"),
              encoding="utf-8") as stream:
        record = json.load(stream)
    return {
        name: [
            (factor, np.frombuffer(bytes.fromhex(value), dtype=np.uint8).reshape(4, 4))
            for factor, value in record["relators"][name]["word"]
        ]
        for name in RELATOR_ORDER
    }


def main():
    group, chart = atlas_m23_and_a8()
    source = GL(4, GF(2))
    isomorphism = libgap.IsomorphismGroups(source, chart)
    if isomorphism == libgap.fail:
        raise AssertionError("GAP did not identify GL4(2) with maximal A8")

    def image(value, graph=False):
        if graph:
            value = gf2_inv(value).T.copy()
        return isomorphism.Image(source(value.tolist())._libgap_())

    double_cosets = list(group.DoubleCosets(chart, chart))
    sizes = [int(cell.Size()) for cell in double_cosets]
    if sorted(sizes) != [20160, 302400, 4233600, 5644800]:
        raise AssertionError("M23 double-coset sizes changed")

    scanner = libgap.eval(r"""
function(G, cells, words)
  local one, records, cell, firstFailure, survivors, first, g, gi,
        i, w, pair, value, letter, good;
  one := One(G);
  records := [];
  first := fail;
  for cell in cells do
    firstFailure := List([1..Length(words)], i -> 0);
    survivors := 0;
    for g in cell do
      gi := g^-1;
      good := true;
      for i in [1..Length(words)] do
        w := words[i];
        value := one;
        for pair in w do
          letter := pair[2];
          if pair[1] = 2 then letter := g * letter * gi; fi;
          value := value * letter;
        od;
        if value <> one then
          firstFailure[i] := firstFailure[i] + 1;
          good := false;
          break;
        fi;
      od;
      if good then
        survivors := survivors + 1;
        if first = fail then first := g; fi;
      fi;
    od;
    Add(records, [Size(cell), firstFailure, survivors]);
  od;
  return [records, first];
end
""")

    words = load_words()
    parities = {}
    for parity, graph in (("inner", False), ("graph", True)):
        gap_words = libgap([
            [[factor, image(value, graph and factor == 2)] for factor, value in words[name]]
            for name in RELATOR_ORDER
        ])
        result = scanner(group, libgap(double_cosets), gap_words)
        records = []
        for row in result[0]:
            histogram = {
                name: int(row[1][index])
                for index, name in enumerate(RELATOR_ORDER)
            }
            survivors = int(row[2])
            if sum(histogram.values()) + survivors != int(row[0]):
                raise AssertionError("cell census does not sum to its size")
            records.append({
                "size": int(row[0]),
                "first_failure_histogram": histogram,
                "survivor_count": survivors,
            })
        parities[parity] = {
            "double_coset_records": records,
            "survivor_count": sum(row["survivor_count"] for row in records),
            "first_survivor": None if result[1] == libgap.fail else str(result[1]),
        }

    print(json.dumps({
        "overgroup": "M23",
        "overgroup_order": int(group.Size()),
        "chart_order": int(chart.Size()),
        "chart_index": int(group.Index(chart)),
        "chart_normalizer_order": int(group.Normalizer(chart).Size()),
        "double_coset_sizes": sizes,
        "relators": list(RELATOR_ORDER),
        "marking_parities": parities,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
