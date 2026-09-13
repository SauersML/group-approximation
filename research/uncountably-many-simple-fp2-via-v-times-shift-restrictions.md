---
rg: 2
id: uncountably-many-simple-fp2-via-v-times-shift-restrictions
kind: route
title: "Uncountably many simple FP_2 groups from perfect restriction kernels of an FP_2 alternating full group"
target: uncountably-many-simple-groups-of-type-fp2
requires:
  - v-times-shift-alternating-group-is-of-type-fp2
  - v-times-shift-restriction-kernels-are-perfect
  - v-times-shift-alternating-group-restrictions-are-simple
  - fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup
---

Let `H = A(G)` with `G = G_V × (Z ⋉ {0,1}^Z)`.

- `H` is of type FP_2 (first prerequisite), hence finitely generated.
- For each infinite minimal subshift `Y`, the restriction `ρ_Y` is onto the
  simple group `A(G|_{C×Y})` (third prerequisite), with perfect kernel `K_Y`
  (second prerequisite).
- So `A(G|_{C×Y}) ≅ H/K_Y` is of type FP_2 by consequence 1 of
  `fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup`.

There are `2^aleph_0` such `Y` with pairwise distinct kernels (third
prerequisite). `H` is finitely generated, so a countable simple group is the
quotient `H/K` for at most countably many `K`. Hence these simple FP_2 groups
realize uncountably many isomorphism types. This is the counting step of
`simple-fp2-uncountability-via-perfect-simple-quotients-proof`, applied with
the FP_2 group `H` in place of a finitely presented one.

The first two prerequisites are open. The route is a genuine reduction: both
can fail independently of the target.
