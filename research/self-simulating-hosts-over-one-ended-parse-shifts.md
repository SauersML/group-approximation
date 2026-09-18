---
rg: 2
id: self-simulating-hosts-over-one-ended-parse-shifts
kind: claim
title: (OPEN) Self-simulating hosts over one-ended parse shifts, where telescope fixed points indexed by a locally uniquely parsable hierarchy over a one-ended decidable group generate a finitely presented full group carrying the seed at every infinite-level point
requires:
  - telescope-fixed-points-are-singular-on-a-parse-shift
  - boone-higman-via-v-times-aperiodic-sft-full-groups
  - quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products
distinct_from:
  boone-higman-via-v-times-aperiodic-sft-full-groups: that route asks for finite presentation of the V-stabilized full group of Λ ⋉ X for a quantum-rigid SFT X; this adds the telescope fixed points θ_s, which carry a seed group in the isotropy of every infinite-level point, and asks for finite presentation of the enlarged host. It is the group-side mechanism in which the cross-depth relations ARE the parse rule.
---

**OPEN.** Nothing below is proved beyond the one-chain facts of
`telescope-fixed-points-are-singular-on-a-parse-shift`.

**The shape.** The one-chain fixed point `θ_s` is a Cantor homeomorphism with three features:
- it simulates the seed `s` at the first level where the hierarchical parse terminates;
- it fixes the parse shift `Y` of never-terminating parses, which is an SFT;
- it carries `⟨S⟩` in its germ at every point of `Y`.

Along one chain the parse shift is one-dimensional, so the host is PSPACE-capped (item 5
there). The multidimensional version replaces the chain by a hierarchy indexed by a one-ended
group.

**Conjecture SS.** There are:
- a finitely presented one-ended group `Λ` with solvable word problem;
- a fixed-point (self-simulating) SFT `X ⊂ A^Λ` whose hierarchical parse is locally unique, meaning the
  level-`k` supertile of the origin is determined by a window of radius `r_k` (Durand–Romashchenko–Shen type);

such that three things hold:
1. **(Fixed points.)** For every homeomorphism `s` of the label space `L`, the "act by `s` at the first
   level where the origin's parse terminates" equation has a unique solution `θ_s` on
   `X × L^ω`. Its singular set is the infinite-level set `Y_∞ ⊂ X`, a closed shift-invariant set of
   configurations whose origin is a corner of every level.
2. **(Finiteness.)** For finite `S`, the group `𝕋 = ⟨F(G_V × Λ⋉X), θ_S⟩` is finitely presented and has
   an fp simple commutator-type subgroup. Here `F(G_V × Λ⋉X)` is the V-stabilized full group of the
   master route.
3. **(Reach.)** The isotropy of `𝕋` at every point of `Y_∞` contains `⟨S⟩ ≅ θ_S`.

**Why it is the right target:**
- **Cross-depth rule.** In `𝕋` the cross-depth relations are the parse rule. The relation
  `θ_s = (s at level 0, θ_s at deeper levels)` becomes, in the Λ-indexed version, "`θ_s` commutes
  with the level-raising parse maps up to the seed". That is the unique deep solution demanded by
  bh-free-22's locality principle.
- **Rigidity.** Locally unique parse is the proposed source of quantum rigidity (Conjecture G2-fp,
  board/SYNTHESIS.md). By `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`, rigidity
  already gives the ring-side crossed product. Item 2 is the group side (P2′) with the extra
  generators `θ_S`.
- **Complexity.** It escapes bh-free-32's PSPACE cap in the only allowed way: the parse of `X` is a
  Λ-hierarchy, so hardness enters through the word problem of `Λ` and the language of `X`.
- **Where the input goes.**
  - Seeds only propagate. By `telescopic-germ-bases-in-v-germ-extensions-are-v-separated`
    item 5, a simple input must already lie in `⟨S⟩`.
  - So the design places the input `G ≤ Λ` through the shift action.
  - The seeds `θ_S` supply the self-similarity that item 2 needs for finite presentation. They do
    not supply the input.

**First tests, in order:**
- **(T1) One chain.** Identify the full-group closure of `⟨V, θ_S⟩` over the golden-mean parse shift
  `Y`, where `S ⊂ V` is finite. Prove it finitely presented. The expected answer is a
  Matui / Katsura–Exel–Pardo SFT full group. This is the calibration.
- **(T2) Z².** Write `θ_s` for a DRS fixed-point tiling. Compute `Y_∞` (the infinite-level faults), and
  test whether item 2 reduces to Conjecture G2-fp plus bh-g3-steinfarley's non-LCM finiteness
  theorem.
- **(T3) Non-amenable Λ.** Repeat over `F₂ × F₂`, a Mozes-type or Baumslag–Solitar hierarchy
  (bh-g2-fixedpoint-b).

**Lesson for general BH.** Self-simulation gives a concrete candidate for the "compiler" of the
wrapper∘actor picture. The actor is `Λ` acting on a locally uniquely parsable hierarchy. The
self-similarity that makes the wrapper finitely presented is realized by telescope fixed points
whose singular set is the infinite-level set. The test is whether "unique parse" gives finite
presentation over one-ended `Λ` as it does along one chain.
