#!/usr/bin/env sage
"""Exact seed-fiber calibration for the ten marked O8+(2) packet screens.

This script deliberately does not enumerate the 174,182,400 ambient
conjugators.  It constructs the six ambient A8 classes, installs the two
GL(4,2) markings, and uses character-table class multiplication constants to
count the conjugator fiber selected by each of the sixteen factor-oriented
packet edges.  The output chooses the sharp seed for each of the ten screens;
it is the required bounded preflight before any exact fiber replay.
"""

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sage.all import GF, GL, libgap

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word


def six_charts(group):
    maximals = list(libgap.MaximalSubgroupClassReps(group))
    affine = [subgroup for subgroup in maximals if int(subgroup.Size()) == 1290240]
    if len(affine) != 3:
        raise AssertionError("O8+(2) affine triality carrier count changed")

    by_label = {}
    normalizer_order = {}
    for carrier_index, carrier in enumerate(affine, start=1):
        translations = [
            subgroup for subgroup in carrier.NormalSubgroups()
            if int(subgroup.Size()) == 64 and bool(subgroup.IsElementaryAbelian())
        ]
        if len(translations) != 1:
            raise AssertionError("affine carrier lost its unique normal 2^6")
        local = list(libgap.ComplementClassesRepresentatives(carrier, translations[0]))
        if len(local) != 2:
            raise AssertionError("affine complement count changed")
        for local_index, chart in enumerate(local, start=1):
            label = (carrier_index, local_index)
            by_label[label] = chart
            normalizer_order[label] = int(group.Normalizer(chart).Size())

    natural = {}
    orthogonal = {}
    for carrier in [subgroup for subgroup in maximals if int(subgroup.Size()) == 181440]:
        candidates = [
            subgroup for subgroup in libgap.MaximalSubgroupClassReps(carrier)
            if int(subgroup.Size()) == 20160
        ]
        if len(candidates) != 1:
            raise AssertionError("A9 natural A8 class changed")
        chart = candidates[0]
        labels = [label for label, affine_chart in by_label.items()
                  if bool(group.IsConjugate(chart, affine_chart))]
        if len(labels) != 1:
            raise AssertionError("natural A8 has nonunique affine fusion label")
        natural[labels[0][0]] = by_label[labels[0]]
    for carrier in [subgroup for subgroup in maximals if int(subgroup.Size()) == 1451520]:
        candidates = [
            subgroup.DerivedSubgroup()
            for subgroup in libgap.MaximalSubgroupClassReps(carrier)
            if int(subgroup.Size()) == 40320
            and int(subgroup.DerivedSubgroup().Size()) == 20160
        ]
        if len(candidates) != 1:
            raise AssertionError("S6(2) orthogonal A8 class changed")
        chart = candidates[0]
        labels = [label for label, affine_chart in by_label.items()
                  if bool(group.IsConjugate(chart, affine_chart))]
        if len(labels) != 1:
            raise AssertionError("orthogonal A8 has nonunique affine fusion label")
        orthogonal[labels[0][0]] = by_label[labels[0]]

    if sorted(natural) != [1, 2, 3] or sorted(orthogonal) != [1, 2, 3]:
        raise AssertionError("triality indexing of natural/orthogonal classes changed")
    for index in [1, 2, 3]:
        if int(group.Normalizer(natural[index]).Size()) != 20160:
            raise AssertionError("natural chart is no longer self-normalized")
        if int(group.Normalizer(orthogonal[index]).Size()) != 40320:
            raise AssertionError("orthogonal chart lost its S8 normalizer")
    return natural, orthogonal


def relations():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    selected = [word for _index, word in select_packet(words, x_lengths())]
    distinct = {}
    for word in selected:
        by_factor = {factor: matrix for factor, matrix in word}
        first, second = by_factor[1], by_factor[2]
        distinct.setdefault((first.tobytes(), second.tobytes()), (first, second))
    if len(distinct) != 16:
        raise AssertionError("factor-oriented packet edge count changed")
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])
    return list(distinct.values()), collision


def graph_matrix(matrix, source):
    """The contragredient outer automorphism of GL(4,2)."""
    return source(matrix.tolist()).inverse().matrix().transpose()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--full-screens",
        help="comma-separated zero-based marked-screen indices to replay",
    )
    args = parser.parse_args()

    group = libgap.PrimitiveGroup(135, 2)
    if int(group.Size()) != 174182400:
        raise AssertionError("O8+(2) order changed")
    natural, orthogonal = six_charts(group)
    edges, collision = relations()
    source = GL(4, GF(2))

    screen_specs = [
        ("N1-N2", natural[1], natural[2], [0, 1]),
        ("O1-O2", orthogonal[1], orthogonal[2], [0]),
        ("N1-O1", natural[1], orthogonal[1], [0, 1]),
        ("N1-O2", natural[1], orthogonal[2], [0, 1]),
        ("N1-N1-outside-A9", natural[1], natural[1], [0, 1]),
        ("O1-O1-outside-S6", orthogonal[1], orthogonal[1], [0]),
    ]

    classes = list(libgap.ConjugacyClasses(group))
    representatives = [conjugacy_class.Representative() for conjugacy_class in classes]
    class_sizes = [int(conjugacy_class.Size()) for conjugacy_class in classes]
    table = libgap.CharacterTable(group)
    class_orders = [int(value) for value in libgap.OrdersClassRepresentatives(table)]
    table_sizes = [int(value) for value in libgap.SizesConjugacyClasses(table)]
    if table_sizes != class_sizes:
        raise AssertionError("group/table conjugacy-class ordering mismatch")
    target_classes = [index for index, order in enumerate(class_orders, start=1)
                      if order in (1, 3)]

    class_cache = {}

    def class_index(element):
        key = str(element)
        if key not in class_cache:
            hits = [index for index, representative in enumerate(representatives, start=1)
                    if bool(group.IsConjugate(element, representative))]
            if len(hits) != 1:
                raise AssertionError("element has nonunique ambient class")
            class_cache[key] = hits[0]
        return class_cache[key]

    requested = set()
    if args.full_screens:
        requested = {int(value) for value in args.full_screens.split(",")}
        if any(value < 0 or value >= 10 for value in requested):
            raise ValueError("full-screen index is outside 0..9")

    scanner = libgap.eval(r"""
function(G, edges, collision, seedIndex, expectedSeedCandidates)
  local one, seed, x, y, class, centralizer, seedCandidates, packetTotal,
        collisionTotal, collisionOrders, firstPacketConjugator,
        firstCollisionValue, yp, g0, c, g, good, i, edge, value, pair,
        letter, orderValue, orderPosition;
  one := One(G);
  seed := edges[seedIndex]; x := seed[1]; y := seed[2];
  class := ConjugacyClass(G,y);
  centralizer := Centralizer(G,y);
  seedCandidates := 0; packetTotal := 0; collisionTotal := 0;
  collisionOrders := []; firstPacketConjugator := fail;
  firstCollisionValue := fail;
  for yp in class do
    if IsOne((x*yp)^3) then
      g0 := RepresentativeAction(G,y,yp);
      for c in centralizer do
        seedCandidates := seedCandidates+1;
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
          if firstPacketConjugator=fail then firstPacketConjugator:=g; fi;
          value := one;
          for pair in collision do
            letter := pair[2];
            if pair[1]=2 then letter := letter^g; fi;
            value := value*letter;
          od;
          if value=one then
            collisionTotal := collisionTotal+1;
          else
            if firstCollisionValue=fail then firstCollisionValue:=value; fi;
            orderValue := Order(value);
            orderPosition := Position(List(collisionOrders,row->row[1]),orderValue);
            if orderPosition=fail then
              Add(collisionOrders,[orderValue,1]);
            else
              collisionOrders[orderPosition][2] :=
                collisionOrders[orderPosition][2]+1;
            fi;
          fi;
        fi;
      od;
    fi;
  od;
  if seedCandidates<>expectedSeedCandidates then
    Error("class multiplication and explicit seed-fiber counts disagree");
  fi;
  Sort(collisionOrders,function(a,b) return a[1]<b[1]; end);
  return [seedCandidates,packetTotal,collisionTotal,collisionOrders,
          firstPacketConjugator,firstCollisionValue];
end
""")

    output_screens = []
    marked_index = 0
    expected_full = {
        0: (1492992, 0, 0, {}),
        1: (1492992, 0, 0, {}),
        2: (8957952, 2776, 0, {2: 2256, 4: 520}),
        3: (1492992, 0, 0, {}),
        4: (1492992, 0, 0, {}),
        5: (1492992, 0, 0, {}),
        6: (1492992, 0, 0, {}),
        7: (1492992, 208, 0, {2: 176, 4: 32}),
        8: (1492992, 208, 0, {2: 176, 4: 32}),
        9: (8957952, 2776, 0, {2: 2256, 4: 520}),
    }
    for name, first_chart, second_chart, parities in screen_specs:
        first_iso = libgap.IsomorphismGroups(source, first_chart)
        second_iso = libgap.IsomorphismGroups(source, second_chart)
        if first_iso == libgap.fail or second_iso == libgap.fail:
            raise AssertionError("GL4(2) chart identification failed")
        for parity in parities:
            records = []
            for edge_index, (first, second) in enumerate(edges, start=1):
                first_element = first_iso.Image(source(first.tolist())._libgap_())
                marked_second = graph_matrix(second, source) if parity else second
                second_source = source(marked_second) if parity else source(marked_second.tolist())
                second_element = second_iso.Image(second_source._libgap_())
                first_class = class_index(first_element)
                second_class = class_index(second_element)
                compatible = 0
                for product_class in target_classes:
                    coefficient = int(libgap.ClassMultiplicationCoefficient(
                        table, first_class, second_class, product_class
                    ))
                    numerator = coefficient * class_sizes[product_class - 1]
                    if numerator % class_sizes[first_class - 1] != 0:
                        raise AssertionError("nonintegral fixed-first class count")
                    compatible += numerator // class_sizes[first_class - 1]
                centralizer_order = int(group.Centralizer(second_element).Size())
                records.append({
                    "edge": edge_index,
                    "first_ambient_class": first_class,
                    "second_ambient_class": second_class,
                    "compatible_second_conjugates": compatible,
                    "second_centralizer_order": centralizer_order,
                    "conjugator_fiber_candidates": compatible * centralizer_order,
                })
            best = min(records, key=lambda record: record["conjugator_fiber_candidates"])
            screen_output = {
                "marked_screen_index": marked_index,
                "screen": name,
                "relative_graph_parity": parity,
                "best_seed_edge": best["edge"],
                "best_seed_conjugator_fiber_candidates":
                    best["conjugator_fiber_candidates"],
                "seed_edge_records": records,
            }

            if marked_index in requested:
                matrices = {}
                for first, second in edges:
                    matrices.setdefault(first.tobytes(), first)
                    matrices.setdefault(second.tobytes(), second)
                for _factor, matrix in collision:
                    matrices.setdefault(matrix.tobytes(), matrix)
                first_images = {
                    key: first_iso.Image(source(matrix.tolist())._libgap_())
                    for key, matrix in matrices.items()
                }
                second_images = {}
                for key, matrix in matrices.items():
                    marked = graph_matrix(matrix, source) if parity else matrix
                    marked_source = source(marked) if parity else source(marked.tolist())
                    second_images[key] = second_iso.Image(marked_source._libgap_())
                gap_edges = libgap([
                    [first_images[first.tobytes()], second_images[second.tobytes()]]
                    for first, second in edges
                ])
                gap_collision = libgap([
                    [factor, (first_images if factor == 1 else second_images)[matrix.tobytes()]]
                    for factor, matrix in collision
                ])
                result = scanner(
                    group,
                    gap_edges,
                    gap_collision,
                    best["edge"],
                    best["conjugator_fiber_candidates"],
                )
                actual = (
                    int(result[0]),
                    int(result[1]),
                    int(result[2]),
                    {int(row[0]): int(row[1]) for row in result[3]},
                )
                if actual != expected_full[marked_index]:
                    raise AssertionError(
                        f"marked screen {marked_index} changed: {actual}"
                    )
                screen_output["full_screen"] = {
                    "seed_candidates_explicitly_replayed": int(result[0]),
                    "packet_survivors": int(result[1]),
                    "packet_and_19243_survivors": int(result[2]),
                    "nonidentity_19243_order_histogram": {
                        str(int(row[0])): int(row[1]) for row in result[3]
                    },
                    "first_packet_conjugator": (
                        None if result[4] == libgap.fail else str(result[4])
                    ),
                    "first_nonidentity_19243_value": (
                        None if result[5] == libgap.fail else str(result[5])
                    ),
                }
            output_screens.append(screen_output)
            marked_index += 1

    print(json.dumps({
        "ambient": "O8+(2)",
        "ambient_order": int(group.Size()),
        "factor_oriented_packet_edges": len(edges),
        "marked_screens": len(output_screens),
        "method": "character-table class multiplication, no ambient conjugator scan",
        "screens": output_screens,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
