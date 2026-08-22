#!/usr/bin/env sage
"""Exact seed-fiber Atlas packet screen in the unique M24 A8 class."""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sage.all import GF, GL, libgap

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word
from atlas_two_chart_search import gf2_inv


def relations():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet_words = [word for _index, word in select_packet(words, x_lengths())]
    distinct = {}
    for word in packet_words:
        by_factor = {factor: matrix for factor, matrix in word}
        first, second = by_factor[1], by_factor[2]
        distinct.setdefault((first.tobytes(), second.tobytes()), (first, second))
    if len(distinct) != 16:
        raise AssertionError("factor-oriented packet edge count changed")
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])
    q14 = words[14]
    return list(distinct.values()), collision, q14


def main():
    group = libgap.MathieuGroup(24)
    octad = libgap.Set([24, 3, 6, 9, 23, 19, 15, 5])
    point = 1
    carrier = libgap.Stabilizer(group, octad, libgap.OnSets)
    chart = carrier.Stabilizer(point)
    if (int(group.Size()), int(carrier.Size()), int(chart.Size())) != (
        244823040, 322560, 20160,
    ):
        raise AssertionError("M24 canonical anti-flag calibration changed")
    if int(group.Normalizer(chart).Size()) != 20160:
        raise AssertionError("M24 A8 chart stopped being self-normalizing")

    source = GL(4, GF(2))
    isomorphism = libgap.IsomorphismGroups(source, chart)
    if isomorphism == libgap.fail:
        raise AssertionError("GAP did not identify GL(4,2) with the M24 chart")
    edges, collision, q14 = relations()
    matrices = {}
    for first, second in edges:
        matrices.setdefault(first.tobytes(), first)
        matrices.setdefault(second.tobytes(), second)
    for word in (collision, q14):
        for _factor, matrix in word:
            matrices.setdefault(matrix.tobytes(), matrix)

    def image(matrix, graph=False):
        if graph:
            matrix = gf2_inv(matrix).T.copy()
        return isomorphism.Image(source(matrix.tolist())._libgap_())

    scanner = libgap.eval(r"""
function(G,A,O,p,edges,collision,q14,seedIndex)
  local one, seed, x, y, class, centralizer, seedCandidates, packetTotal,
        collisionTotal, q14Total, jointTotal, cells, yp, g0, c, g, good,
        i, edge, value, pair, letter, cgood, qgood, B, fixed, orbits,
        octads, C, fiber, degree, key, position, row, orderValue, orderPosition;
  one:=One(G); seed:=edges[seedIndex]; x:=seed[1]; y:=seed[2];
  class:=ConjugacyClass(G,y); centralizer:=Centralizer(G,y);
  seedCandidates:=0; packetTotal:=0; collisionTotal:=0; q14Total:=0;
  jointTotal:=0; cells:=[];
  for yp in class do
    if IsOne((x*yp)^3) then
      g0:=RepresentativeAction(G,y,yp);
      for c in centralizer do
        seedCandidates:=seedCandidates+1; g:=c*g0; good:=true;
        for i in [1..Length(edges)] do
          if i<>seedIndex then
            edge:=edges[i];
            if not IsOne((edge[1]*(edge[2]^g))^3) then
              good:=false; break;
            fi;
          fi;
        od;
        if good then
          packetTotal:=packetTotal+1;
          B:=A^g;
          fixed:=Filtered([1..24],q->ForAll(GeneratorsOfGroup(B),h->q^h=q));
          if Length(fixed)<>1 then Error("packet chart lost unique fixed point"); fi;
          orbits:=Orbits(B,[1..24],OnPoints);
          octads:=Filtered(orbits,orbit->Length(orbit)=8);
          if Length(octads)<>1 then Error("packet chart lost unique octad orbit"); fi;
          C:=Set(octads[1]);
          if fixed[1]=p then fiber:="fixed";
          elif fixed[1] in O then fiber:="octad";
          else fiber:="nonzero_affine"; fi;
          degree:=Size(A)/Size(Intersection(A,B));
          key:=[fiber,degree,Size(Intersection(O,C)),p in C,O=C];
          position:=Position(List(cells,row->row[1]),key);
          if position=fail then
            Add(cells,[key,0,0,0,0,[]]); position:=Length(cells);
          fi;
          row:=cells[position]; row[2]:=row[2]+1;

          value:=one;
          for pair in collision do
            letter:=pair[2]; if pair[1]=2 then letter:=letter^g; fi;
            value:=value*letter;
          od;
          cgood:=value=one;
          if cgood then collisionTotal:=collisionTotal+1; row[3]:=row[3]+1;
          else
            orderValue:=Order(value);
            orderPosition:=Position(List(row[6],entry->entry[1]),orderValue);
            if orderPosition=fail then Add(row[6],[orderValue,1]);
            else row[6][orderPosition][2]:=row[6][orderPosition][2]+1; fi;
          fi;

          value:=one;
          for pair in q14 do
            letter:=pair[2]; if pair[1]=2 then letter:=letter^g; fi;
            value:=value*letter;
          od;
          qgood:=value=one;
          if qgood then q14Total:=q14Total+1; row[4]:=row[4]+1; fi;
          if cgood and qgood then jointTotal:=jointTotal+1; row[5]:=row[5]+1; fi;
        fi;
      od;
    fi;
  od;
  for row in cells do
    Sort(row[6],function(left,right)return left[1]<right[1];end);
  od;
  Sort(cells,function(left,right)
    if left[1][1]<>right[1][1] then return left[1][1]<right[1][1];fi;
    return left[1][2]<right[1][2];
  end);
  return [seedCandidates,packetTotal,collisionTotal,q14Total,jointTotal,cells];
end
""")

    parity_results = {}
    for parity, graph in (("inner", False), ("graph", True)):
        gap_edges = libgap([
            [image(first), image(second, graph)] for first, second in edges
        ])
        gap_collision = libgap([
            [factor, image(matrix, graph and factor == 2)]
            for factor, matrix in collision
        ])
        gap_q14 = libgap([
            [factor, image(matrix, graph and factor == 2)]
            for factor, matrix in q14
        ])
        result = scanner(
            group, chart, octad, point, gap_edges, gap_collision, gap_q14, 1,
        )
        cells = []
        for row in result[5]:
            key = row[0]
            cells.append({
                "fiber": str(key[0]),
                "subdegree": int(key[1]),
                "octad_intersection": int(key[2]),
                "base_point_in_target_octad": bool(key[3]),
                "same_octad": bool(key[4]),
                "packet_survivors": int(row[1]),
                "packet_and_19243_survivors": int(row[2]),
                "packet_and_q14_survivors": int(row[3]),
                "joint_survivors": int(row[4]),
                "nonidentity_19243_order_histogram": {
                    str(int(entry[0])): int(entry[1]) for entry in row[5]
                },
            })
        parity_results[parity] = {
            "seed_candidates_explicitly_replayed": int(result[0]),
            "packet_survivors": int(result[1]),
            "packet_and_19243_survivors": int(result[2]),
            "packet_and_q14_survivors": int(result[3]),
            "joint_survivors": int(result[4]),
            "cells_with_packet_survivors": cells,
        }

    expected = {
        "inner": {
            "seed": 5806080,
            "totals": (57, 0, 19, 0),
            "cells": [
                ("fixed", 1, 8, False, True, 30, 0, 11, 0, {"2": 25, "4": 5}),
                ("nonzero_affine", 15, 8, False, True, 27, 0, 8, 0,
                 {"2": 22, "4": 5}),
            ],
        },
        "graph": {
            "seed": 5806080,
            "totals": (57, 0, 20, 0),
            "cells": [
                ("fixed", 1, 8, False, True, 30, 0, 10, 0, {"2": 25, "4": 5}),
                ("nonzero_affine", 15, 8, False, True, 27, 0, 10, 0,
                 {"2": 22, "4": 5}),
            ],
        },
    }
    for parity, calibration in expected.items():
        actual = parity_results[parity]
        totals = (
            actual["packet_survivors"],
            actual["packet_and_19243_survivors"],
            actual["packet_and_q14_survivors"],
            actual["joint_survivors"],
        )
        cells = [
            (
                cell["fiber"], cell["subdegree"], cell["octad_intersection"],
                cell["base_point_in_target_octad"], cell["same_octad"],
                cell["packet_survivors"], cell["packet_and_19243_survivors"],
                cell["packet_and_q14_survivors"], cell["joint_survivors"],
                cell["nonidentity_19243_order_histogram"],
            )
            for cell in actual["cells_with_packet_survivors"]
        ]
        if actual["seed_candidates_explicitly_replayed"] != calibration["seed"]:
            raise AssertionError(f"{parity} M24 seed count changed")
        if totals != calibration["totals"]:
            raise AssertionError(f"{parity} M24 packet totals changed: {totals}")
        if cells != calibration["cells"]:
            raise AssertionError(f"{parity} M24 packet cells changed: {cells}")

    print(json.dumps({
        "ambient": "M24",
        "ambient_order": int(group.Size()),
        "chart_order": int(chart.Size()),
        "chart_normalizer_order": int(group.Normalizer(chart).Size()),
        "factor_oriented_packet_edges": len(edges),
        "seed_edge": 1,
        "parities": parity_results,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
