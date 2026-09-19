---
rg: 2
id: boone-higman-via-fp-stabilizer-engines
kind: route
title: Embed the input in a finitely presented decidable group B_0 (Clapham), double it to B = B_0 wr Z/2 so that the input lies in [B, B], and take the derived full group of Z/2 * B on its compactified Bass–Serre tree
target: boone-higman-conjecture
requires:
  - clapham-fp-embedding-preserves-word-problem
  - free-product-boundary-groupoids-carry-the-vertex-group-homology
  - fp-decidable-vertex-groups-have-fp-stabilizer-engines
distinct_from:
  boone-higman-via-stabilizer-engines: that put the input in a decidable SIMPLE envelope and is circular (stabilizer-engines-of-non-fp-simple-groups-are-not-fp); this puts it in a finitely presented decidable group, which is what finite presentation of the engine requires.
---

Let `G` be a finitely generated group with solvable word problem. We may assume `G` is
infinite, since finite groups embed in Thompson's `V`.

1. **Clapham.** `G` embeds in a finitely presented group `B_0` with solvable word problem
   (`clapham-fp-embedding-preserves-word-problem`).
2. **Doubling.** Put `B = B_0 ≀ Z/2 = (B_0 × B_0) ⋊ ⟨τ⟩`, with `τ` swapping the factors.
   - `B` is finitely presented, infinite and has solvable word problem.
   - The map `g ↦ (g, g^{-1})` is an injective homomorphism `G -> B_0 × B_0`.
   - Its image lies in `[B, B]`: `(g, g^{-1}) = [(g, 1), τ]`.
3. **The engine.** `B <= F_B`, so `[B, B] <= [F_B, F_B] = D(F_B)`. `D(F_B)` is simple
   (`free-product-boundary-groupoids-carry-the-vertex-group-homology`) and finitely presented
   by the open `fp-decidable-vertex-groups-have-fp-stabilizer-engines`. So `G` embeds in a
   finitely presented simple group. `∎`

**Status. REFUTED as stated (2026-09-18).** Step 3 rests on
`fp-decidable-vertex-groups-have-fp-stabilizer-engines`, which fails at `B = Z`. A finitely
presented engine needs an isolated vertex group (`stabilizer-engines-force-isolated-vertex-groups`),
and `B_0 ≀ Z/2` is not finitely discriminable whenever `B_0` is residually finite. The live form is
`boone-higman-via-isolated-stabilizer-engines`. Historical note: the two hypotheses used here
(finitely presented, decidable) are necessary but not sufficient.

## Lesson for general BH

Simplicity is free here: the engine's derived full group is simple for every infinite `B`, and
the doubling trick puts any subgroup into the derived subgroup. Finite presentation is the
whole problem, and it is confined to one emitter with a finitely presented, decidable germ
group. So Track C is Boone–Higman "for one vertex": no global coding is needed.
