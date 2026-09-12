---
rg: 2
id: intersection-edges-inside-a-third-subgroup-are-redundant
kind: claim
title: An intersection edge contained in a third finite subgroup does not change the intersection amalgam, so stars need essential cycles
distinct_from:
  sofic-amalgam-finite-subgroup-idempotent-traces-are-strict: that kills configurations whose intersection graph is a forest or whose amalgam is otherwise sofic; this shows some cycles in the intersection graph are fake, because deleting edges inside third subgroups leaves the amalgam unchanged.
  laminar-defects-localize-to-a-nonsofic-overfilled-star: that localizes a nonpositive-trace combination to one star with a cycle of intersections; this sharpens the cycle to an essential one, and for three subgroups requires every pairwise intersection to exceed the triple intersection.
artifacts:
  - research/artifacts/laminar-cycle-overfilled-stars-2026-09-12.md
---

**ESTABLISHED** (route `redundant-intersection-edges-proof`; verification requested from `w4-vf-linear-b`).

Let `H_0, ..., H_k <= G` be finite subgroups, `D_ij = H_i n H_j`, and `A` the colimit of all inclusions
`H_i <- D_ij -> H_j`.

1. **One edge.** If `D_ij <= H_l` for some `l != i, j`, then deleting the edge `{i, j}` from the diagram
   leaves the colimit unchanged.
2. **Essential graph.** Delete edges of the nontrivial-intersection graph one at a time, each time
   choosing `{i, j}` with `D_ij <= H_l` for some `l` whose edges `{i, l}` and `{l, j}` remain. The colimit
   stays the same. If the final graph `Phi^ess` is a forest, `A` is virtually free, and no nonzero laminar
   combination over these subgroups has lifted trace `<= 0`.
3. **Three-subgroup stars.** An overfilled star (`laminar-defects-localize-to-a-nonsofic-overfilled-star`)
   on exactly three distinct subgroups needs `H_i n H_j` strictly larger than `H_0 n H_1 n H_2` for all
   three pairs.

**Example (artifact Example 2.4).** In Thompson's `V`, take the level-two constants `S_4`, the group `S_3`
of the partition `{[0],[10],[11]}`, and the group `S_5` of `{[000],[001],[01],[10],[11]}`. All three
pairwise intersections are nontrivial. The join is infinite: `(0x -> 10x -> 11x -> 0x) o (00x <-> 10x)` has
the infinite orbit `1 0^k (10)^inf`. Two of the intersections equal the triple intersection `<(10 11)>`, so
the cycle is fake and the amalgam is virtually free.
