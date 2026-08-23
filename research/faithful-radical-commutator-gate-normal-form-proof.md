---
rg: 2
id: faithful-radical-commutator-gate-normal-form-proof
kind: route
title: Read the four alternating syllables and use normality of the transported radical
target: faithful-radical-commutator-gate
requires: [mf-radical-functoriality]
artifacts:
  - GroupApproximation/Algebra/FaithfulRadicalCocycle.lean
---

Transport `z` along the canonical map `H -> H * B`.  Normality puts its
commutator with every right-factor element in the transported radical, and
subgroup commutator calculus places it in the derived radical layer.

If `z` and `b` are nontrivial, `[z,b]` is the reduced word with factor pattern
`H,B,H,B`, so it is nontrivial.  Equality of two gate outputs reduces to a
right-factor element commuting with `z`; the same four-syllable criterion
forces that element to be trivial.  Applying the free-product map induced by
`B -> C` proves naturality, and direct group multiplication proves the cocycle
identity.
