#!/usr/bin/env sage
"""Exact six-relator screen in the unique A8 class of Sp(6,2).

This is the first CFSG candidate-specific check after reducing every finite
six-relator escape to a larger finite simple marked-A8 overgroup.  The first
chart is the derived A8 of an S8 maximal subgroup.  One exact GAP loop tests
every relative marked conjugator against the six frozen free-product words.
"""

import json
import os

import numpy as np
from sage.all import GF, GL, libgap


RELATOR_ORDER = ("s_0", "s_11", "s_30", "s_44", "s_55", "c_19243")


def load_words():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-six-relator-relative-pieces.json"),
              encoding="utf-8") as stream:
        record = json.load(stream)
    words = {}
    matrices = {}
    for name in RELATOR_ORDER:
        word = []
        for factor, value in record["relators"][name]["word"]:
            matrix = np.frombuffer(bytes.fromhex(value), dtype=np.uint8).reshape(4, 4)
            key = bytes(matrix.reshape(-1))
            matrices[key] = matrix
            word.append((factor, key))
        words[name] = word
    return words, matrices


def main():
    group = libgap.Sp(6, 2)
    s8_maximals = [subgroup for subgroup in group.MaximalSubgroups()
                   if int(subgroup.Size()) == 40320]
    chart = s8_maximals[0].DerivedSubgroup()
    if int(chart.Size()) != 20160:
        raise AssertionError("derived S8 subgroup is not A8")
    if any(not bool(group.IsConjugate(chart, subgroup.DerivedSubgroup()))
           for subgroup in s8_maximals):
        raise AssertionError("the S8-derived A8 subgroups split into classes")

    source = GL(4, GF(2))
    isomorphism = libgap.IsomorphismGroups(source, chart)
    if isomorphism == libgap.fail:
        raise AssertionError("GAP did not identify GL(4,2) with the chart A8")

    words, matrices = load_words()
    images = {
        key: isomorphism.Image(source(matrix.tolist())._libgap_())
        for key, matrix in matrices.items()
    }
    gap_words = libgap([
        [[factor, images[key]] for factor, key in words[name]]
        for name in RELATOR_ORDER
    ])

    scanner = libgap.eval(r"""
function(G, words)
  local one, firstFailure, survivors, first, g, gi, i, w, pair,
        value, letter, good;
  one := One(G);
  firstFailure := List([1..Length(words)], i -> 0);
  survivors := 0;
  first := fail;
  for g in G do
    gi := g^-1;
    good := true;
    for i in [1..Length(words)] do
      w := words[i];
      value := one;
      for pair in w do
        letter := pair[2];
        if pair[1] = 2 then
          letter := g * letter * gi;
        fi;
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
  return [firstFailure, survivors, first];
end
""")
    result = scanner(group, gap_words)
    first = result[2]
    histogram = {
        name: int(result[0][index])
        for index, name in enumerate(RELATOR_ORDER)
    }
    if sum(histogram.values()) + int(result[1]) != int(group.Size()):
        raise AssertionError("first-failure census does not sum to group order")

    print(json.dumps({
        "overgroup": "Sp(6,2)",
        "overgroup_order": int(group.Size()),
        "s8_maximal_subgroups": len(s8_maximals),
        "s8_derived_a8_one_conjugacy_class": True,
        "chart_order": int(chart.Size()),
        "chart_normalizer_order": int(group.Normalizer(chart).Size()),
        "conjugators_tested": int(group.Size()),
        "relators": list(RELATOR_ORDER),
        "first_failure_histogram": histogram,
        "survivor_count": int(result[1]),
        "first_survivor": None if first == libgap.fail else str(first),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
