#!/usr/bin/env sage
"""Exact six-relator screens for the subfield A8 in L4(4).

The computation uses the 85-point projective action of GL(4,4).  Its scalar
kernel has order three and its image is PGL(4,4)=PSL(4,4), so every relative
projective conjugator occurs exactly once.  Permutation multiplication makes
the 5.5-million-element seed fibers substantially faster than matrix replay.

The standard subfield chart has two relative marking parities, the identity
and the graph automorphism g |-> (g^-1)^T.  This script screens both.  It
does not assert that every abstract A8 subgroup of L4(4) is conjugate to the
subfield chart.
"""

import json
import os
from itertools import product

import numpy as np
from sage.all import GF, GL, Matrix, SymmetricGroup, libgap, vector


RELATOR_ORDER = ("s_0", "s_11", "s_30", "s_44", "s_55", "c_19243")


def load_words():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(
        os.path.join(here, "atlas-six-relator-relative-pieces.json"),
        encoding="utf-8",
    ) as stream:
        record = json.load(stream)
    return {
        name: [
            (
                factor,
                np.frombuffer(bytes.fromhex(value), dtype=np.uint8).reshape(4, 4),
            )
            for factor, value in record["relators"][name]["word"]
        ]
        for name in RELATOR_ORDER
    }


def projective_action(field):
    """Return the right action of GL(4,field) on normalized row lines."""

    points = {}
    values = list(field)
    for entries in product(values, repeat=4):
        if not any(entries):
            continue
        pivot = next(entry for entry in entries if entry)
        normalized = tuple(entry / pivot for entry in entries)
        points[normalized] = None
    point_list = list(points)
    if len(point_list) != 85:
        raise AssertionError("PG(3,4) no longer has 85 points")
    index = {point: position + 1 for position, point in enumerate(point_list)}
    symmetric = SymmetricGroup(85)

    def image(matrix):
        images = []
        for point in point_list:
            moved = vector(field, point) * matrix
            pivot = next(entry for entry in moved if entry)
            normalized = tuple(entry / pivot for entry in moved)
            images.append(index[normalized])
        return symmetric(images)

    return image


def main():
    binary = GF(2)
    field = GF(4, "z")
    source = GL(4, binary)
    linear = GL(4, field)
    project = projective_action(field)
    group = libgap.Group(
        [project(generator.matrix())._libgap_() for generator in linear.gens()]
    )
    if int(group.Size()) != 987033600:
        raise AssertionError("projective GL(4,4) image order changed")

    source_generators = [
        project(Matrix(field, generator.matrix()))._libgap_()
        for generator in source.gens()
    ]
    chart = libgap.Group(source_generators)
    if int(chart.Size()) != 20160:
        raise AssertionError("subfield GL(4,2) chart order changed")
    if int(group.Centralizer(chart).Size()) != 1:
        raise AssertionError("projective subfield chart centralizer is nontrivial")

    words = load_words()
    scanner = libgap.eval(
        r"""
function(G, words)
  local one, seed, x0, a, c, d, class, centralizer,
        seedClassHits, seedCandidates, firstFailure,
        survivors, first, x, g0, z, g, i, w, pair, value, letter, good;
  one := One(G);
  seed := words[1];
  if Length(seed)<>6 or seed[1][1]<>2 or seed[2][1]<>1 or
     seed[3][1]<>2 or seed[4][1]<>1 or seed[5][1]<>2 or
     seed[6][1]<>1 or seed[1][2]<>seed[3][2] or
     seed[1][2]<>seed[5][2] then
    Error("s_0 lost its x A x C x D seed form");
  fi;
  x0 := seed[1][2]; a := seed[2][2]; c := seed[4][2]; d := seed[6][2];
  class := ConjugacyClass(G,x0);
  centralizer := Centralizer(G,x0);
  seedClassHits := 0; seedCandidates := 0;
  firstFailure := List([2..Length(words)], i -> 0);
  survivors := 0; first := fail;
  for x in class do
    if IsOne(x*a*x*c*x*d) then
      seedClassHits := seedClassHits+1;
      g0 := RepresentativeAction(G,x0,x);
      if g0=fail or x0^g0<>x then
        Error("conjugacy representative action failed");
      fi;
      for z in centralizer do
        seedCandidates := seedCandidates+1;
        g := z*g0;
        good := true;
        for i in [2..Length(words)] do
          w := words[i]; value := one;
          for pair in w do
            letter := pair[2];
            if pair[1]=2 then letter := letter^g; fi;
            value := value*letter;
          od;
          if value<>one then
            firstFailure[i-1] := firstFailure[i-1]+1;
            good := false; break;
          fi;
        od;
        if good then
          survivors := survivors+1;
          if first=fail then first:=g; fi;
        fi;
      od;
    fi;
  od;
  if seedCandidates<>seedClassHits*Size(centralizer) then
    Error("projective seed fibers do not have centralizer size");
  fi;
  return [Size(class),Size(centralizer),seedClassHits,seedCandidates,
          firstFailure,survivors,first];
end
"""
    )

    def image(matrix, graph=False):
        value = source(Matrix(binary, matrix.tolist()))
        if graph:
            value = source(value.inverse().matrix().transpose())
        return project(Matrix(field, value.matrix()))._libgap_()

    screens = []
    for parity, graph in (("inner", False), ("graph", True)):
        gap_words = []
        for name in RELATOR_ORDER:
            gap_words.append(
                [
                    [factor, image(matrix, graph and factor == 2)]
                    for factor, matrix in words[name]
                ]
            )
        result = scanner(group, libgap(gap_words))
        failures = {
            name: int(result[4][index])
            for index, name in enumerate(RELATOR_ORDER[1:])
        }
        if sum(failures.values()) + int(result[5]) != int(result[3]):
            raise AssertionError("post-seed census does not sum to seed fiber")
        screens.append(
            {
                "relative_marking": parity,
                "s_0_conjugacy_class_size": int(result[0]),
                "projective_seed_centralizer_size": int(result[1]),
                "s_0_conjugacy_class_hits": int(result[2]),
                "s_0_projective_conjugator_candidates": int(result[3]),
                "post_s_0_first_failure_histogram": failures,
                "survivor_count": int(result[5]),
                "first_survivor": (
                    None if result[6] == libgap.fail else str(result[6])
                ),
            }
        )

    output = {
        "overgroup": "L4(4)",
        "overgroup_order": 987033600,
        "screened_chart": "standard subfield GL4(2)",
        "subfield_chart_order": int(chart.Size()),
        "projective_subfield_chart_centralizer_order": int(
            group.Centralizer(chart).Size()
        ),
        "relative_markings": 2,
        "relators": list(RELATOR_ORDER),
        "screens": screens,
        "total_survivors": sum(row["survivor_count"] for row in screens),
    }
    for row in screens:
        if (
            row["s_0_conjugacy_class_size"] != 5355
            or row["projective_seed_centralizer_size"] != 184320
            or row["s_0_conjugacy_class_hits"] != 30
            or row["s_0_projective_conjugator_candidates"] != 5529600
        ):
            raise AssertionError("L4(4) seed calibration changed")
    expected_failures = {
        "inner": {
            "s_11": 5528592,
            "s_30": 864,
            "s_44": 108,
            "s_55": 27,
            "c_19243": 9,
        },
        "graph": {
            "s_11": 5529600,
            "s_30": 0,
            "s_44": 0,
            "s_55": 0,
            "c_19243": 0,
        },
    }
    for row in screens:
        if (
            row["post_s_0_first_failure_histogram"]
            != expected_failures[row["relative_marking"]]
            or row["survivor_count"] != 0
            or row["first_survivor"] is not None
        ):
            raise AssertionError("L4(4) six-relator census changed")
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
