#!/usr/bin/env sage
"""Exact six-relator screens for all ten marked A8-pair types in O8+(2).

The ambient group has order 174,182,400, so a literal tenfold conjugator
scan is unnecessary.  The first relator has the special form

    x A x C x D = 1,

where ``x`` is one conjugate of a fixed element of the second chart.  We
first enumerate that conjugacy class, then replay only the corresponding
centralizer fibers.  This is an exact partition of the conjugators satisfying
the first relator; the remaining five words are multiplied literally.
"""

import argparse
import json
import os

import numpy as np
from sage.all import GF, GL, libgap

from atlas_o8p2_ten_packet_screens import graph_matrix, six_charts


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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--screens",
        default="0,1,2,3,4,5,6,7,8,9",
        help="comma-separated zero-based marked-screen indices",
    )
    args = parser.parse_args()
    requested = {int(value) for value in args.screens.split(",") if value}
    if any(value < 0 or value >= 10 for value in requested):
        raise ValueError("screen index is outside 0..9")

    group = libgap.PrimitiveGroup(135, 2)
    if int(group.Size()) != 174182400:
        raise AssertionError("O8+(2) order changed")
    natural, orthogonal = six_charts(group)
    source = GL(4, GF(2))
    words = load_words()

    screen_specs = [
        ("N1-N2", natural[1], natural[2], [0, 1]),
        ("O1-O2", orthogonal[1], orthogonal[2], [0]),
        ("N1-O1", natural[1], orthogonal[1], [0, 1]),
        ("N1-O2", natural[1], orthogonal[2], [0, 1]),
        ("N1-N1", natural[1], natural[1], [0, 1]),
        ("O1-O1", orthogonal[1], orthogonal[1], [0]),
    ]

    scanner = libgap.eval(r"""
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
""")

    output = []
    marked_index = 0
    for name, first_chart, second_chart, parities in screen_specs:
        first_iso = libgap.IsomorphismGroups(source, first_chart)
        second_iso = libgap.IsomorphismGroups(source, second_chart)
        if first_iso == libgap.fail or second_iso == libgap.fail:
            raise AssertionError("GL4(2) chart identification failed")

        for parity in parities:
            this_index = marked_index
            marked_index += 1
            if this_index not in requested:
                continue

            gap_words = []
            for relator_name in RELATOR_ORDER:
                gap_word = []
                for factor, matrix in words[relator_name]:
                    if factor == 1:
                        element = first_iso.Image(source(matrix.tolist())._libgap_())
                    else:
                        marked = graph_matrix(matrix, source) if parity else matrix
                        marked_source = source(marked) if parity else source(marked.tolist())
                        element = second_iso.Image(marked_source._libgap_())
                    gap_word.append([factor, element])
                gap_words.append(gap_word)

            result = scanner(group, libgap(gap_words))
            failures = {
                relator_name: int(result[4][index])
                for index, relator_name in enumerate(RELATOR_ORDER[1:])
            }
            if sum(failures.values()) + int(result[5]) != int(result[3]):
                raise AssertionError("post-seed census does not sum to seed fiber")
            output.append({
                "marked_screen_index": this_index,
                "screen": name,
                "relative_graph_parity": parity,
                "s_0_conjugacy_class_size": int(result[0]),
                "s_0_seed_centralizer_order": int(result[1]),
                "s_0_conjugacy_class_hits": int(result[2]),
                "s_0_conjugator_fiber_candidates": int(result[3]),
                "post_s_0_first_failure_histogram": failures,
                "survivor_count": int(result[5]),
                "first_survivor": None if result[6] == libgap.fail else str(result[6]),
            })

    print(json.dumps({
        "overgroup": "O8+(2)",
        "overgroup_order": int(group.Size()),
        "marked_screens_requested": sorted(requested),
        "marked_screens_completed": len(output),
        "relators": list(RELATOR_ORDER),
        "screens": output,
        "total_survivors": sum(row["survivor_count"] for row in output),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
