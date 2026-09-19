#!/usr/bin/env sage
"""Exact six-relator screen for both marked A8 parities in GL(5,2).

The subgroup H=diag(GL(4,2),1) is the unique A8 class in PSL(5,2), but its
normalizer does not induce the outer automorphism.  We therefore run the
ambient conjugator census twice: once with the standard marking and once
after inverse-transpose on every factor-two label.
"""

import json
import os

import numpy as np
from sage.all import GF, libgap, matrix


RELATOR_ORDER = ("s_0", "s_11", "s_30", "s_44", "s_55", "c_19243")


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


def graph(matrix4):
    return np.asarray(
        matrix(GF(2), matrix4.tolist()).inverse().transpose(), dtype=np.uint8
    )


def embed(matrix4):
    value = matrix.identity(GF(2), 5)
    for row in range(4):
        for column in range(4):
            value[row, column] = int(matrix4[row, column])
    return value._libgap_()


def gap_words(words, dual_second, permutation_isomorphism):
    output = []
    for name in RELATOR_ORDER:
        word = []
        for factor, value in words[name]:
            if factor == 2 and dual_second:
                value = graph(value)
            word.append([factor, permutation_isomorphism.Image(embed(value))])
        output.append(word)
    return libgap(output)


def main():
    matrix_group = libgap.GL(5, 2)
    source_generators = libgap.GL(4, 2).GeneratorsOfGroup()
    matrix_chart = libgap.Subgroup(matrix_group, libgap([
        embed(np.asarray(generator.sage(), dtype=np.uint8))
        for generator in source_generators
    ]))
    if int(matrix_chart.Size()) != 20160:
        raise AssertionError("standard GL4(2) chart has wrong order")
    if int(matrix_group.Normalizer(matrix_chart).Size()) != 20160:
        raise AssertionError("standard chart normalizer changed")
    permutation_isomorphism = matrix_group.IsomorphismPermGroup()
    group = permutation_isomorphism.Image()
    chart = permutation_isomorphism.Image(matrix_chart)
    # GAP chooses the faithful action on all 32 vectors (zero is fixed), rather
    # than deleting the fixed point to report the equivalent degree-31 action.
    if int(group.LargestMovedPoint()) != 32:
        raise AssertionError("GL5(2) permutation image is not the natural vector action")

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

    words = load_words()
    parities = {}
    for name, dual in (("natural", False), ("dual", True)):
        result = scanner(group, gap_words(words, dual, permutation_isomorphism))
        histogram = {
            relator: int(result[0][index])
            for index, relator in enumerate(RELATOR_ORDER)
        }
        survivors = int(result[1])
        if sum(histogram.values()) + survivors != int(group.Size()):
            raise AssertionError("first-failure census does not sum to group order")
        parities[name] = {
            "first_failure_histogram": histogram,
            "survivor_count": survivors,
            "first_survivor": None if result[2] == libgap.fail else str(result[2]),
        }

    print(json.dumps({
        "overgroup": "GL(5,2)=PSL(5,2)",
        "overgroup_order": int(group.Size()),
        "chart_order": int(chart.Size()),
        "chart_index": int(group.Index(chart)),
        "chart_normalizer_order": int(group.Normalizer(chart).Size()),
        "permutation_degree": int(group.LargestMovedPoint()),
        "conjugators_per_parity": int(group.Size()),
        "relators": list(RELATOR_ORDER),
        "marking_parities": parities,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
