#!/usr/bin/env sage
"""Exact Atlas six-relator screen for every marked natural A8 pair in A12.

Every nontrivial A8 action on at most twelve points is the natural
eight-point action plus fixed points.  The A12 normalizer of a fixed chart
induces all of ``Aut(A8)``, so varying one ambient conjugator covers all
relative markings.  The seed-fiber kernel is the same exact partition used
for the orthogonal endpoint screens.
"""

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
    group = libgap.AlternatingGroup(12)
    chart = libgap.AlternatingGroup(8)
    if int(group.Size()) != 239500800 or not bool(group.IsSubgroup(chart)):
        raise AssertionError("natural A8<A12 calibration changed")
    normalizer = group.Normalizer(chart)
    centralizer = group.Centralizer(chart)
    if int(normalizer.Size()) != 483840:
        raise AssertionError("natural A8 normalizer in A12 changed")
    if int(centralizer.Size()) != 12:
        raise AssertionError("natural A8 centralizer in A12 changed")
    if int(normalizer.Size()) // int(centralizer.Size()) != 40320:
        raise AssertionError("A12 normalizer no longer realizes Aut(A8)")

    source = GL(4, GF(2))
    marking = libgap.IsomorphismGroups(source, chart)
    if marking == libgap.fail:
        raise AssertionError("GAP did not identify GL(4,2) with natural A8")
    words = load_words()
    gap_words = []
    for name in RELATOR_ORDER:
        gap_word = []
        for factor, matrix in words[name]:
            element = marking.Image(source(matrix.tolist())._libgap_())
            gap_word.append([factor, element])
        gap_words.append(gap_word)

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
    result = scanner(group, libgap(gap_words))
    failures = {
        name: int(result[4][index])
        for index, name in enumerate(RELATOR_ORDER[1:])
    }
    if sum(failures.values()) + int(result[5]) != int(result[3]):
        raise AssertionError("post-seed census does not sum to seed fiber")
    print(
        json.dumps(
            {
                "overgroup": "A12",
                "overgroup_order": int(group.Size()),
                "A8_action": [8, 1, 1, 1, 1],
                "A8_normalizer_order": int(normalizer.Size()),
                "A8_centralizer_order": int(centralizer.Size()),
                "outer_marking_absorbed_by_normalizer": True,
                "relators": list(RELATOR_ORDER),
                "s_0_conjugacy_class_size": int(result[0]),
                "s_0_seed_centralizer_order": int(result[1]),
                "s_0_conjugacy_class_hits": int(result[2]),
                "s_0_conjugator_fiber_candidates": int(result[3]),
                "post_s_0_first_failure_histogram": failures,
                "survivor_count": int(result[5]),
                "first_survivor": (
                    None if result[6] == libgap.fail else str(result[6])
                ),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
