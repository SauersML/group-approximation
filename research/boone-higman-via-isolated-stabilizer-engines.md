---
rg: 2
id: boone-higman-via-isolated-stabilizer-engines
kind: route
title: Put G wr Z/2 in an isolated group B (Cornulier–Guyot–Pitsch Question 4), then take the derived full group of Z/2 * B on its compactified Bass–Serre tree
target: boone-higman-conjecture
requires:
  - every-decidable-group-embeds-in-an-isolated-group
  - isolated-vertex-groups-have-fp-stabilizer-engines
  - free-product-boundary-groupoids-carry-the-vertex-group-homology
distinct_from:
  boone-higman-via-fp-stabilizer-engines: that used vertex groups that are only finitely presented and decidable (Clapham), and its engine claim is refuted (free-product-emitter-full-groups-need-isolated-vertex-groups); this is the corrected route sketched in that node's status, as its own node, with isolated vertex groups as finite presentation of the engine requires.
---

Let `G` be finitely generated with solvable word problem. We may take `G` infinite.

1. **Doubling.** `G_1 = G ≀ Z/2` is finitely generated with solvable word problem.
   `g ↦ (g, g^{-1}) = [(g, 1), τ]` embeds `G` in `[G_1, G_1]`.
2. **Isolated overgroup.** By the open `every-decidable-group-embeds-in-an-isolated-group`,
   `G_1 ≤ B` with `B` isolated. We may take `B` infinite.
3. **Engine.** `B ≤ F_B`, so `G ≤ [G_1, G_1] ≤ [B, B] ≤ D(F_B)`.
   - `D(F_B)` is simple (`free-product-boundary-groupoids-carry-the-vertex-group-homology`).
   - It is finitely presented by the open `isolated-vertex-groups-have-fp-stabilizer-engines`. `∎`

**Status.** Open at both steps 2 and 3. Both are forced by the shape of the route.
- Step 2 is implied by Boone–Higman, since finitely presented simple groups are isolated.
- The hypothesis of step 3 is necessary (`free-product-emitter-full-groups-need-isolated-vertex-groups`, `stabilizer-engines-are-fp-only-over-isolated-groups`).

## Lesson for general BH

Track C splits Boone–Higman into two halves:
- a group-theoretic half (make the input isolated);
- a dynamical half (turn an isolated emitter into a finitely presented simple host).

The earlier forms of the route tried to skip the first half, first with simple envelopes and
then with Clapham envelopes. The continuity obstruction shows that it cannot be skipped.
