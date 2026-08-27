#!/usr/bin/env sage
"""Exact conjugacy-fiber screen for the HS S8-derived A8 equality family."""

import argparse
import json
import os
import sys
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sage.all import GF, GL, libgap

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word


BASE = "https://brauer.maths.qmul.ac.uk/Atlas/spor/HS/gap/"
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


def hs_and_s8():
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
    if libgap.IsomorphismGroups(chart, libgap.AlternatingGroup(8)) == libgap.fail:
        raise AssertionError("ATLAS max5 subgroup is not the S8 class")
    return group, normalizer, chart


def load_relations():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet_words = [word for _index, word in select_packet(words, x_lengths())]
    distinct = {}
    for word in packet_words:
        by_factor = {factor: matrix for factor, matrix in word}
        first, second = by_factor[1], by_factor[2]
        distinct.setdefault((first.tobytes(), second.tobytes()), (first, second))
    if len(distinct) != 16:
        raise AssertionError(
            f"packet factor-oriented distinct-edge count changed to {len(distinct)}"
        )
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])
    q14 = words[14]
    return list(distinct.values()), collision, q14


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed-only", action="store_true")
    args = parser.parse_args()

    group, normalizer, chart = hs_and_s8()
    source = GL(4, GF(2))
    isomorphism = libgap.IsomorphismGroups(source, chart)
    edges, collision, q14 = load_relations()
    matrices = {}
    for first, second in edges:
        matrices.setdefault(first.tobytes(), first)
        matrices.setdefault(second.tobytes(), second)
    for word in (collision, q14):
        for _factor, matrix in word:
            matrices.setdefault(matrix.tobytes(), matrix)
    images = {
        key: isomorphism.Image(source(matrix.tolist())._libgap_())
        for key, matrix in matrices.items()
    }
    gap_edges = libgap([
        [images[first.tobytes()], images[second.tobytes()]]
        for first, second in edges
    ])

    seed_counter = libgap.eval(r"""
function(G, edges)
  local records, i, x, y, class, count, z;
  records := [];
  for i in [1..Length(edges)] do
    x := edges[i][1]; y := edges[i][2];
    class := ConjugacyClass(G,y);
    count := 0;
    for z in class do
      if IsOne((x*z)^3) then count := count+1; fi;
    od;
    Add(records,[i,Order(x),Order(y),Size(class),Size(Centralizer(G,y)),count,
      count*Size(Centralizer(G,y))]);
  od;
  return records;
end
""")
    records = [[int(entry) for entry in row] for row in seed_counter(group, gap_edges)]
    output = {
        "ambient": "HS",
        "ambient_order": int(group.Size()),
        "normalizer": "S8",
        "normalizer_order": int(normalizer.Size()),
        "chart": "A8",
        "chart_order": int(chart.Size()),
        "distinct_packet_edges": len(edges),
        "seed_edge_records": [
            {
                "edge": row[0],
                "first_order": row[1],
                "second_order": row[2],
                "second_ambient_class_size": row[3],
                "second_ambient_centralizer_order": row[4],
                "compatible_conjugates": row[5],
                "conjugator_fiber_candidates": row[6],
            }
            for row in records
        ],
        "best_seed_edge": min(records, key=lambda row: row[6])[0],
    }
    if not args.seed_only:
        def gap_word(word):
            return libgap([
                [factor, images[matrix.tobytes()]] for factor, matrix in word
            ])

        scanner = libgap.eval(r"""
function(G, M, edges, collision, q14, seedIndex)
  local one, seed, x, y, class, centralizer, cells, packetTotal,
        collisionTotal, q14Total, jointTotal, collisionOrders, firstJoint,
        yp, g0, c, g, good, i, edge, value, pair, letter, cgood, qgood,
        intersectionOrder, cellIndex, orderValue, orderPosition;
  one := One(G);
  seed := edges[seedIndex]; x := seed[1]; y := seed[2];
  class := ConjugacyClass(G,y);
  centralizer := Centralizer(G,y);
  cells := List([40320,1440,384,120,64], order -> [order,0,0,0,0]);
  packetTotal := 0; collisionTotal := 0; q14Total := 0; jointTotal := 0;
  collisionOrders := [];
  firstJoint := fail;
  for yp in class do
    if IsOne((x*yp)^3) then
      g0 := RepresentativeAction(G,y,yp);
      for c in centralizer do
        g := c*g0;
        good := true;
        for i in [1..Length(edges)] do
          if i <> seedIndex then
            edge := edges[i];
            if not IsOne((edge[1]*(edge[2]^g))^3) then
              good := false; break;
            fi;
          fi;
        od;
        if good then
          packetTotal := packetTotal+1;
          intersectionOrder := Size(Intersection(M,M^g));
          cellIndex := Position(List(cells,row->row[1]),intersectionOrder);
          if cellIndex = fail then Error("unknown S8 double-coset cell"); fi;
          cells[cellIndex][2] := cells[cellIndex][2]+1;

          value := one;
          for pair in collision do
            letter := pair[2];
            if pair[1]=2 then letter := letter^g; fi;
            value := value*letter;
          od;
          cgood := value=one;
          if cgood then
            collisionTotal := collisionTotal+1;
            cells[cellIndex][3] := cells[cellIndex][3]+1;
          else
            orderValue := Order(value);
            orderPosition := Position(List(collisionOrders,row->row[1]),orderValue);
            if orderPosition=fail then
              Add(collisionOrders,[orderValue,1]);
            else
              collisionOrders[orderPosition][2] := collisionOrders[orderPosition][2]+1;
            fi;
          fi;

          value := one;
          for pair in q14 do
            letter := pair[2];
            if pair[1]=2 then letter := letter^g; fi;
            value := value*letter;
          od;
          qgood := value=one;
          if qgood then
            q14Total := q14Total+1;
            cells[cellIndex][4] := cells[cellIndex][4]+1;
          fi;
          if cgood and qgood then
            jointTotal := jointTotal+1;
            cells[cellIndex][5] := cells[cellIndex][5]+1;
            if firstJoint=fail then firstJoint:=g; fi;
          fi;
        fi;
      od;
    fi;
  od;
  Sort(collisionOrders,function(a,b) return a[1]<b[1]; end);
  return [packetTotal,collisionTotal,q14Total,jointTotal,cells,
          collisionOrders,firstJoint];
end
""")
        seed_index = min(records, key=lambda row: row[6])[0]
        result = scanner(
            group,
            normalizer,
            gap_edges,
            gap_word(collision),
            gap_word(q14),
            seed_index,
        )
        expected_cells = [
            [40320, 60, 0, 21, 0],
            [1440, 0, 0, 0, 0],
            [384, 0, 0, 0, 0],
            [120, 0, 0, 0, 0],
            [64, 0, 0, 0, 0],
        ]
        actual_cells = [[int(value) for value in row] for row in result[4]]
        if actual_cells != expected_cells:
            raise AssertionError(f"HS double-coset packet screen changed: {actual_cells}")
        if [int(result[index]) for index in range(4)] != [60, 0, 21, 0]:
            raise AssertionError("HS packet/collision totals changed")
        if [[int(value) for value in row] for row in result[5]] != [[2, 50], [4, 10]]:
            raise AssertionError("HS collision-value order histogram changed")
        if result[6] != libgap.fail:
            raise AssertionError("unexpected HS joint survivor")
        output["full_screen"] = {
            "seed_edge": seed_index,
            "packet_survivors": int(result[0]),
            "packet_and_19243_survivors": int(result[1]),
            "packet_and_q14_survivors": int(result[2]),
            "joint_survivors": int(result[3]),
            "cells": [
                {
                    "S8_intersection_order": int(row[0]),
                    "packet_survivors": int(row[1]),
                    "packet_and_19243_survivors": int(row[2]),
                    "packet_and_q14_survivors": int(row[3]),
                    "joint_survivors": int(row[4]),
                }
                for row in result[4]
            ],
            "nonidentity_collision_order_histogram": {
                str(int(row[0])): int(row[1]) for row in result[5]
            },
            "first_joint_survivor": None if result[6] == libgap.fail else str(result[6]),
        }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
