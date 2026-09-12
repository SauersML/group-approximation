#!/usr/bin/env sage
"""Exact six-relator screen over the S8 double cosets of HS."""

import json
import os
import urllib.request

import numpy as np
from sage.all import GF, GL, libgap


BASE = "https://brauer.maths.qmul.ac.uk/Atlas/spor/HS/gap/"
RELATOR_ORDER = ("s_0", "s_11", "s_30", "s_44", "s_55", "c_19243")
MAX5_SLP = (
    ("mu", 1, 2, 3), ("mu", 3, 2, 4), ("mu", 3, 4, 5),
    ("mu", 3, 5, 6), ("mu", 6, 3, 7), ("mu", 7, 4, 8),
    ("mu", 3, 8, 9), ("mu", 9, 4, 10), ("mu", 10, 10, 11),
    ("mu", 10, 11, 1), ("mu", 3, 3, 5), ("mu", 3, 5, 7),
    ("mu", 7, 7, 5), ("iv", 5, 7), ("mu", 7, 1, 10),
    ("mu", 10, 5, 1), ("mu", 4, 4, 5), ("mu", 4, 5, 7),
    ("iv", 7, 8), ("mu", 7, 6, 3), ("mu", 3, 8, 2),
)


def atlas_permutation(filename):
    text = urllib.request.urlopen(BASE + filename, timeout=30).read().decode("ascii")
    expression = text.split(":=", 1)[1].strip()
    if expression.endswith(";"):
        expression = expression[:-1]
    return libgap.eval(expression)


def hs_and_chart():
    a = atlas_permutation("HSG1-p100B0.g1")
    b = atlas_permutation("HSG1-p100B0.g2")
    group = libgap.Group([a, b])
    registers = {1: a, 2: b}
    for operation in MAX5_SLP:
        if operation[0] == "mu":
            _, left, right, target = operation
            registers[target] = registers[left] * registers[right]
        else:
            _, source, target = operation
            registers[target] = registers[source] ** -1
    normalizer = libgap.Group([registers[1], registers[2]])
    chart = normalizer.DerivedSubgroup()
    if (int(group.Size()), int(normalizer.Size()), int(chart.Size())) != (
        44352000, 40320, 20160
    ):
        raise AssertionError("HS/S8/A8 orders changed")
    return group, normalizer, chart


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
    group, normalizer, chart = hs_and_chart()
    source = GL(4, GF(2))
    isomorphism = libgap.IsomorphismGroups(source, chart)
    words = load_words()

    def image(value):
        return isomorphism.Image(source(value.tolist())._libgap_())

    gap_words = libgap([
        [[factor, image(value)] for factor, value in words[name]]
        for name in RELATOR_ORDER
    ])
    cells = list(group.DoubleCosets(normalizer, normalizer))
    if sum(int(cell.Size()) for cell in cells) != int(group.Size()):
        raise AssertionError("S8 double cosets do not partition HS")

    scanner = libgap.eval(r"""
function(G, M, cells, words)
  local one, records, cell, representative, intersectionOrder, firstFailure,
        survivors, first, g, gi, i, w, pair, value, letter, good;
  one := One(G);
  records := [];
  first := fail;
  for cell in cells do
    representative := Representative(cell);
    intersectionOrder := Size(Intersection(M,M^representative));
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
          if pair[1]=2 then letter := g*letter*gi; fi;
          value := value*letter;
        od;
        if value<>one then
          firstFailure[i] := firstFailure[i]+1;
          good := false;
          break;
        fi;
      od;
      if good then
        survivors := survivors+1;
        if first=fail then first:=g; fi;
      fi;
    od;
    Add(records,[Size(cell),intersectionOrder,firstFailure,survivors]);
  od;
  return [records,first];
end
""")
    result = scanner(group, normalizer, libgap(cells), gap_words)
    records = []
    for row in result[0]:
        histogram = {
            name: int(row[2][index])
            for index, name in enumerate(RELATOR_ORDER)
        }
        survivors = int(row[3])
        if sum(histogram.values()) + survivors != int(row[0]):
            raise AssertionError("cell census does not sum to its size")
        records.append({
            "size": int(row[0]),
            "S8_intersection_order": int(row[1]),
            "first_failure_histogram": histogram,
            "survivor_count": survivors,
        })

    print(json.dumps({
        "overgroup": "HS",
        "overgroup_order": int(group.Size()),
        "chart_order": int(chart.Size()),
        "chart_index": int(group.Index(chart)),
        "chart_normalizer_order": int(normalizer.Size()),
        "double_cosets": len(cells),
        "double_coset_records": records,
        "survivor_count": sum(row["survivor_count"] for row in records),
        "first_survivor": None if result[1] == libgap.fail else str(result[1]),
        "relators": list(RELATOR_ORDER),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
