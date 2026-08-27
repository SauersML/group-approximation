#!/usr/bin/env sage
"""Exact A4-packet plus collision-19243 screen in Sp(6,2).

The first chart is the derived A8 inside an O_6^+(2):2 ~= S8 maximal
subgroup of Sp(6,2).  The second chart runs through every conjugate labeled
embedding.  The S8 normalizer supplies the outer labeling, so one conjugator
scan covers both automorphism parities.  Evaluation is performed by one GAP
loop; Python only constructs the exact atlas words and the GL(4,2) -> A8 map.
"""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sage.all import GF, GL, libgap

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word


def load_words():
    states, _ = enumerate_ball(5)
    spanning, _, _ = spanning_tree_kernel_words(states)
    packet = [word for _index, word in select_packet(spanning, x_lengths())]
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])
    return packet, collision


def main():
    group = libgap.Sp(6, 2)
    maximals = list(group.MaximalSubgroups())
    s8_maximals = [subgroup for subgroup in maximals if int(subgroup.Size()) == 40320]
    if not s8_maximals:
        raise AssertionError("Sp(6,2) maximal-subgroup list has no S8")
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

    packet, collision = load_words()
    matrices = {}
    for word in packet + [collision]:
        for _factor, matrix in word:
            matrices.setdefault(matrix.tobytes(), matrix)
    images = {
        key: isomorphism.Image(source(matrix.tolist())._libgap_())
        for key, matrix in matrices.items()
    }

    def gap_word(word):
        return libgap([[factor, images[matrix.tobytes()]] for factor, matrix in word])

    gap_packet = libgap([gap_word(word) for word in packet])
    gap_collision = gap_word(collision)
    scanner = libgap.eval(r"""
function(G, packet, collision)
  local one, packetSurvivors, collisionSurvivors, first, g, gi, w, pair,
        value, letter, good;
  one := One(G);
  packetSurvivors := 0;
  collisionSurvivors := 0;
  first := fail;
  for g in G do
    gi := g^-1;
    good := true;
    for w in packet do
      value := one;
      for pair in w do
        letter := pair[2];
        if pair[1] = 2 then
          letter := g * letter * gi;
        fi;
        value := value * letter;
      od;
      if value <> one then
        good := false;
        break;
      fi;
    od;
    if good then
      packetSurvivors := packetSurvivors + 1;
      value := one;
      for pair in collision do
        letter := pair[2];
        if pair[1] = 2 then
          letter := g * letter * gi;
        fi;
        value := value * letter;
      od;
      if value = one then
        collisionSurvivors := collisionSurvivors + 1;
        if first = fail then first := g; fi;
      fi;
    fi;
  od;
  return [packetSurvivors, collisionSurvivors, first];
end
""")
    result = scanner(group, gap_packet, gap_collision)
    first = result[2]
    print(json.dumps({
        "overgroup": "Sp(6,2)",
        "overgroup_order": int(group.Size()),
        "s8_maximal_subgroups": len(s8_maximals),
        "s8_derived_a8_one_conjugacy_class": True,
        "chart_order": int(chart.Size()),
        "chart_normalizer_order": int(group.Normalizer(chart).Size()),
        "conjugators_tested": int(group.Size()),
        "packet_words": len(packet),
        "packet_survivors": int(result[0]),
        "packet_and_collision_survivors": int(result[1]),
        "first_joint_survivor": None if first == libgap.fail else str(first),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
