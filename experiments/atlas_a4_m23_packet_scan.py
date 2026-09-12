#!/usr/bin/env sage
"""Exact double-coset screen for the maximal A8 chart in M23.

The official ATLAS degree-23 standard generators are used literally.  The
ATLAS ``M23G1-max4W1`` straight-line program gives the maximal A8 subgroup H.
The H-H double cosets organize every relative conjugator.  Within each double
coset GAP iterates its elements, testing the 30-word packet first, then
q_19243, then q14.  Both inner and graph parity for the second marked A8 chart
are tested.
"""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sage.all import GF, GL, libgap

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word
from atlas_two_chart_search import gf2_inv


def atlas_m23_and_a8():
    # ATLAS M23G1-p23B0 standard generators.
    a = libgap.eval("(1,2)(3,4)(7,8)(9,10)(13,14)(15,16)(19,20)(21,22)")
    b = libgap.eval(
        "(1,16,11,3)(2,9,21,12)(4,5,8,23)(6,22,14,18)(13,20)(15,17)"
    )
    group = libgap.Group([a, b])

    # ATLAS M23G1-max4W1.  Registers 1 and 2 at exit generate maximal A8.
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
    states, _ = enumerate_ball(5)
    spanning, _, _ = spanning_tree_kernel_words(states)
    packet = [word for _index, word in select_packet(spanning, x_lengths())]
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])
    q14 = spanning[14]
    if [factor for factor, _matrix in q14] != [1, 2, 1, 2]:
        raise AssertionError("q14 factor pattern changed")
    return packet, collision, q14


def main():
    group, chart = atlas_m23_and_a8()
    source = GL(4, GF(2))
    isomorphism = libgap.IsomorphismGroups(source, chart)
    if isomorphism == libgap.fail:
        raise AssertionError("GAP did not identify GL(4,2) with maximal A8")

    packet, collision, q14 = load_words()
    matrices = {}
    for word in packet + [collision, q14]:
        for _factor, matrix in word:
            matrices.setdefault(matrix.tobytes(), matrix)

    def image(matrix, graph=False):
        if graph:
            matrix = gf2_inv(matrix).T.copy()
        return isomorphism.Image(source(matrix.tolist())._libgap_())

    double_cosets = list(group.DoubleCosets(chart, chart))
    double_coset_sizes = [int(value.Size()) for value in double_cosets]
    if sum(double_coset_sizes) != int(group.Size()):
        raise AssertionError("double cosets do not partition M23")
    if sorted(double_coset_sizes) != [20160, 302400, 4233600, 5644800]:
        raise AssertionError("M23 maximal-A8 double-coset sizes changed")

    scanner = libgap.eval(r"""
function(G, H, doubleCosets, packet, collision, q14)
  local one, records, dcIndex, dc, packetCount, collisionCount, q14Count,
        jointCount, first, g, gi, w, pair, value, letter, good, cgood, qgood;
  one := One(G);
  records := [];
  first := fail;
  for dcIndex in [1..Length(doubleCosets)] do
    dc := doubleCosets[dcIndex];
    packetCount := 0;
    collisionCount := 0;
    q14Count := 0;
    jointCount := 0;
    for g in dc do
      gi := g^-1;
      good := true;
      for w in packet do
        value := one;
        for pair in w do
          letter := pair[2];
          if pair[1] = 2 then letter := g * letter * gi; fi;
          value := value * letter;
        od;
        if value <> one then good := false; break; fi;
      od;
      if good then
        packetCount := packetCount + 1;
        value := one;
        for pair in collision do
          letter := pair[2];
          if pair[1] = 2 then letter := g * letter * gi; fi;
          value := value * letter;
        od;
        cgood := value = one;
        if cgood then collisionCount := collisionCount + 1; fi;
        value := one;
        for pair in q14 do
          letter := pair[2];
          if pair[1] = 2 then letter := g * letter * gi; fi;
          value := value * letter;
        od;
        qgood := value = one;
        if qgood then q14Count := q14Count + 1; fi;
        if cgood and qgood then
          jointCount := jointCount + 1;
          if first = fail then first := g; fi;
        fi;
      fi;
    od;
    Add(records,[Size(dc),packetCount,collisionCount,q14Count,jointCount]);
  od;
  return [records,first];
end
""")

    parity_results = {}
    first_escape = None
    for parity, graph in (("inner", False), ("graph", True)):
        def gap_word(word):
            return libgap([
                [factor, image(matrix, graph and factor == 2)]
                for factor, matrix in word
            ])

        result = scanner(
            group,
            chart,
            libgap(double_cosets),
            libgap([gap_word(word) for word in packet]),
            gap_word(collision),
            gap_word(q14),
        )
        rows = [[int(entry) for entry in row] for row in result[0]]
        parity_results[parity] = {
            "double_coset_records": [
                {
                    "size": row[0],
                    "packet_survivors": row[1],
                    "packet_and_19243_survivors": row[2],
                    "packet_and_q14_survivors": row[3],
                    "joint_survivors": row[4],
                }
                for row in rows
            ],
            "packet_survivors": sum(row[1] for row in rows),
            "packet_and_19243_survivors": sum(row[2] for row in rows),
            "packet_and_q14_survivors": sum(row[3] for row in rows),
            "joint_survivors": sum(row[4] for row in rows),
        }
        if result[1] != libgap.fail and first_escape is None:
            first_escape = str(result[1])

    expected = {
        "inner": (30, 0, 11, 0),
        "graph": (30, 0, 10, 0),
    }
    for parity, counts in expected.items():
        actual = parity_results[parity]
        if (
            actual["packet_survivors"],
            actual["packet_and_19243_survivors"],
            actual["packet_and_q14_survivors"],
            actual["joint_survivors"],
        ) != counts:
            raise AssertionError(f"{parity} M23 packet calibration changed")
        if any(
            row["packet_survivors"]
            for row in actual["double_coset_records"]
            if row["size"] != 20160
        ):
            raise AssertionError("packet survivor escaped the identity double coset")

    print(json.dumps({
        "ambient": "M23",
        "ambient_order": int(group.Size()),
        "chart": "A8",
        "chart_order": int(chart.Size()),
        "chart_normalizer_order": int(group.Normalizer(chart).Size()),
        "double_cosets": len(double_cosets),
        "double_coset_size_histogram": {
            str(size): double_coset_sizes.count(size)
            for size in sorted(set(double_coset_sizes))
        },
        "intersection_order_histogram": {
            str(int(chart.Size()) ** 2 // size): double_coset_sizes.count(size)
            for size in sorted(set(double_coset_sizes))
        },
        "packet_words": len(packet),
        "parities": parity_results,
        "first_joint_escape": first_escape,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
