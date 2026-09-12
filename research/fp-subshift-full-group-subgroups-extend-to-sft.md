---
rg: 2
id: fp-subshift-full-group-subgroups-extend-to-sft
kind: claim
title: A finitely presented subgroup of a free subshift's full group extends isomorphically to an SFT neighbourhood
distinct_from:
  thompson-v-not-lef: That records that V is not LEF, via finite presentation and residual finiteness; this extends finitely presented subgroups of subshift full groups to SFT neighbourhoods, which is the dynamical form of that argument.
  amenable-full-group-forces-invariant-measure: That is a measure obstruction for amenable full groups; this is a finite-presentation obstruction for subgroups of subshift full groups, with no amenability hypothesis.
artifacts:
  - research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md
---

**ESTABLISHED.** Let `Lambda` be a finitely generated group, `A` a finite
alphabet, and `X ⊆ A^Lambda` a subshift on which `Lambda` acts freely. Let
`Gamma = <g_1, ..., g_k> <= [[Lambda ~ X]]` be finitely presented.

1. **Extension.** There is a subshift of finite type `Y`, with
   `X ⊆ Y ⊆ A^Lambda`, and elements `hat g_i` in `[[Lambda ~ Y]]` extending the
   `g_i`. Restriction to `X` is an isomorphism `<hat g_i> -> Gamma`.
2. **Simple case.** If `Gamma` is infinite and simple, then for every nonempty
   closed invariant `Z ⊆ Y`, `<hat g_i|_Z>` is trivial or isomorphic to `Gamma`
   through the generators. In particular every `hat g_i` fixes every finite
   `Lambda`-orbit in `Y` pointwise.

**Proof sketch.** The full proof is in the artifact, Section 3.
- The `g_i` and their inverses are local rules.
- The SFT conditions "the formal cocycles of `s_i^{-1} s_i`, `s_i s_i^{-1}` and
  every relator `r_j` are trivial at every translate" hold on `X`, by freeness.
  They cut out `Y`, where the extended generators are homeomorphisms satisfying
  every relator.
- So `s_i -> hat g_i|_Y` is a surjection from `Gamma`, and restriction to `X` is
  its left inverse.
- Item 2 follows because a normal subgroup of a simple group is trivial or
  everything.

This generalizes the ambient-SFT step in Matui's proof of Theorem 5.7
(arXiv:math/0404117, read from source). No novelty is claimed.
