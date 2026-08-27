#!/usr/bin/env sage
"""Exact Atlas six-relator screens for both marked A8 parities in M24."""

import json
import os

import numpy as np
from sage.all import GF, GL, libgap


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


def main():
    group = libgap.MathieuGroup(24)
    octad = libgap.Set([24, 3, 6, 9, 23, 19, 15, 5])
    carrier = libgap.Stabilizer(group, octad, libgap.OnSets)
    chart = carrier.Stabilizer(1)
    if (int(group.Size()), int(carrier.Size()), int(chart.Size())) != (
        244823040,
        322560,
        20160,
    ):
        raise AssertionError("M24 canonical anti-flag calibration changed")
    if int(group.Normalizer(chart).Size()) != 20160:
        raise AssertionError("M24 A8 chart stopped being self-normalizing")
    if int(group.Centralizer(chart).Size()) != 1:
        raise AssertionError("M24 A8 chart centralizer changed")

    source = GL(4, GF(2))
    marking = libgap.IsomorphismGroups(source, chart)
    if marking == libgap.fail:
        raise AssertionError("GAP did not identify GL(4,2) with the M24 chart")
    words = load_words()

    def image(matrix, graph=False):
        value = source(matrix.tolist())
        if graph:
            value = source(value.inverse().matrix().transpose())
        return marking.Image(value._libgap_())

    scanner = libgap.eval(
        r"""
function(G, words)
  local one, seed, x0, a, c, d, class, centralizer, seedClassHits,
        seedCandidates, firstFailure, survivors, first, x, g0, z, g,
        i, w, pair, value, letter, good;
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
    Error("seed conjugator fibers do not have centralizer size");
  fi;
  return [Size(class),Size(centralizer),seedClassHits,seedCandidates,
          firstFailure,survivors,first];
end
"""
    )

    screens = []
    for parity, graph in (("inner", False), ("graph", True)):
        gap_words = []
        for name in RELATOR_ORDER:
            gap_word = []
            for factor, matrix in words[name]:
                gap_word.append([factor, image(matrix, graph and factor == 2)])
            gap_words.append(gap_word)
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
                "s_0_seed_centralizer_order": int(result[1]),
                "s_0_conjugacy_class_hits": int(result[2]),
                "s_0_conjugator_fiber_candidates": int(result[3]),
                "post_s_0_first_failure_histogram": failures,
                "survivor_count": int(result[5]),
                "first_survivor": (
                    None if result[6] == libgap.fail else str(result[6])
                ),
            }
        )

    print(
        json.dumps(
            {
                "overgroup": "M24",
                "overgroup_order": int(group.Size()),
                "A8_conjugacy_classes": 1,
                "A8_normalizer_order": int(group.Normalizer(chart).Size()),
                "A8_centralizer_order": int(group.Centralizer(chart).Size()),
                "relative_markings": 2,
                "relators": list(RELATOR_ORDER),
                "screens": screens,
                "total_survivors": sum(row["survivor_count"] for row in screens),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
