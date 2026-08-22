#!/usr/bin/env sage
"""Exact seed-fiber packet/collision screen in O8-(2)."""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sage.all import GF, GL, libgap

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word


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
    return list(distinct.values()), collision


def main():
    group = libgap.PrimitiveGroup(119, 1)
    maximals = list(libgap.MaximalSubgroupClassReps(group))
    normalizer_candidates = [
        subgroup for subgroup in maximals if int(subgroup.Size()) == 120960
    ]
    if len(normalizer_candidates) != 1:
        raise AssertionError("(3xA8):2 maximal class changed")
    normalizer = normalizer_candidates[0]
    chart_candidates = [
        subgroup for subgroup in normalizer.NormalSubgroups()
        if int(subgroup.Size()) == 20160 and bool(subgroup.IsSimpleGroup())
    ]
    if len(chart_candidates) != 1:
        raise AssertionError("normalizer lost its unique normal A8")
    chart = chart_candidates[0]
    source = GL(4, GF(2))
    isomorphism = libgap.IsomorphismGroups(source, chart)
    edges, collision = relations()

    matrices = {}
    for first, second in edges:
        matrices.setdefault(first.tobytes(), first)
        matrices.setdefault(second.tobytes(), second)
    for _factor, matrix in collision:
        matrices.setdefault(matrix.tobytes(), matrix)
    images = {
        key: isomorphism.Image(source(matrix.tolist())._libgap_())
        for key, matrix in matrices.items()
    }
    gap_edges = libgap([
        [images[first.tobytes()], images[second.tobytes()]]
        for first, second in edges
    ])
    gap_collision = libgap([
        [factor, images[matrix.tobytes()]] for factor, matrix in collision
    ])

    # The sixteen packet edges have only two reversed ambient class-pair types.
    # A literal replay of edge one avoids constructing the very large ordinary
    # character-class multiplication matrix for O8-(2).
    seed_index = 1

    scanner = libgap.eval(r"""
function(G,N,edges,collision,seedIndex)
  local one, seed, x, y, class, centralizer, cells, seedCandidates,
        packetTotal, collisionTotal, yp, g0, c, g, good, i, edge,
        intersectionOrder, cellPosition, value, pair, letter, orderValue,
        orderPosition, firstPacket, firstCollision;
  one:=One(G); seed:=edges[seedIndex]; x:=seed[1]; y:=seed[2];
  class:=ConjugacyClass(G,y); centralizer:=Centralizer(G,y);
  cells:=[[120960,1,0,0,[]],[2160,56,0,0,[]],[1152,105,0,0,[]],
          [192,630,0,0,[]],[144,840,0,0,[]]];
  seedCandidates:=0; packetTotal:=0; collisionTotal:=0;
  firstPacket:=fail; firstCollision:=fail;
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
          if firstPacket=fail then firstPacket:=g; fi;
          intersectionOrder:=Size(Intersection(N,N^g));
          cellPosition:=Position(List(cells,row->row[1]),intersectionOrder);
          if cellPosition=fail then Error("unknown normalizer double-coset cell"); fi;
          cells[cellPosition][3]:=cells[cellPosition][3]+1;
          value:=one;
          for pair in collision do
            letter:=pair[2]; if pair[1]=2 then letter:=letter^g; fi;
            value:=value*letter;
          od;
          if value=one then
            collisionTotal:=collisionTotal+1;
            cells[cellPosition][4]:=cells[cellPosition][4]+1;
          else
            if firstCollision=fail then firstCollision:=value; fi;
            orderValue:=Order(value);
            orderPosition:=Position(List(cells[cellPosition][5],row->row[1]),orderValue);
            if orderPosition=fail then Add(cells[cellPosition][5],[orderValue,1]);
            else cells[cellPosition][5][orderPosition][2]:=
              cells[cellPosition][5][orderPosition][2]+1; fi;
          fi;
        fi;
      od;
    fi;
  od;
  for i in [1..Length(cells)] do
    Sort(cells[i][5],function(a,b) return a[1]<b[1]; end); od;
  return [seedCandidates,packetTotal,collisionTotal,cells,firstPacket,firstCollision];
end
""")
    result = scanner(
        group, normalizer, gap_edges, gap_collision, seed_index,
    )
    cells = [
        {
            "normalizer_intersection_order": int(row[0]),
            "subdegree": int(row[1]),
            "packet_survivors": int(row[2]),
            "packet_and_19243_survivors": int(row[3]),
            "nonidentity_19243_order_histogram": {
                str(int(entry[0])): int(entry[1]) for entry in row[4]
            },
        }
        for row in result[3]
    ]
    expected_cells = [
        (120960, 1, 180, 0, {"2": 150, "4": 30}),
        (2160, 56, 0, 0, {}),
        (1152, 105, 1980, 0, {"2": 1674, "4": 306}),
        (192, 630, 72, 0, {"2": 36, "4": 36}),
        (144, 840, 576, 0, {"2": 504, "4": 72}),
    ]
    actual_cells = [
        (
            cell["normalizer_intersection_order"],
            cell["subdegree"],
            cell["packet_survivors"],
            cell["packet_and_19243_survivors"],
            cell["nonidentity_19243_order_histogram"],
        )
        for cell in cells
    ]
    if actual_cells != expected_cells:
        raise AssertionError(f"O8-(2) packet cell totals changed: {actual_cells}")
    if (int(result[0]), int(result[1]), int(result[2])) != (8294400, 2808, 0):
        raise AssertionError("O8-(2) seed/packet/collision totals changed")
    print(json.dumps({
        "ambient": "O8-(2)",
        "ambient_order": int(group.Size()),
        "A8_normalizer_order": int(normalizer.Size()),
        "factor_oriented_packet_edges": len(edges),
        "relative_graph_parity_absorbed": True,
        "seed_edge": seed_index,
        "seed_count_method": "literal conjugacy class and centralizer fiber",
        "seed_candidates_explicitly_replayed": int(result[0]),
        "packet_survivors": int(result[1]),
        "packet_and_19243_survivors": int(result[2]),
        "cells": cells,
        "first_packet_conjugator": None if result[4] == libgap.fail else str(result[4]),
        "first_nonidentity_19243_value": None if result[5] == libgap.fail else str(result[5]),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
