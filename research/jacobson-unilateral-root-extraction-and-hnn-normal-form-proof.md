---
rg: 2
id: jacobson-unilateral-root-extraction-and-hnn-normal-form-proof
kind: route
title: Extract both unilateral coefficient roots and prove the ascending normal form on the negative tail
target: jacobson-coherent-group-is-an-ascending-corner-extension
requires:
  - jacobson-coherent-quotient-is-faithful-and-has-mf-dichotomy
  - jacobson-shift-representation-is-faithful
  - jacobson-shift-literal-quotient-is-laurent-times-z
  - binary-jacobson-active-cycle-generates-rank-three
artifacts:
  - research/artifacts/jacobson-coherent-group-is-an-ascending-corner-extension-2026-09-08.md
---

The faithful unilateral action gives all finitary matrix units and the
Laurent symbol sequence. Factoring the staggered involution as
`x_12(S)x_21(T)x_12(S)` and conjugating constant roots extracts both
`S` and `T`; third-index commutators then generate every coefficient
of `J`. Thus the original base is exactly `EL_3(J)`.

The corner formula is multiplicative and is recovered by left `T`
and right `S`. It fixes the level-zero block, so its image is proper.
It agrees with bilateral conjugation. Every abstract HNN word reduces
to `t^(-a) A t^b`; identity action on sufficiently negative coordinates
forces `a=b`, and base faithfulness forces `A=I`. Matching symbols and
correcting by a positive finitary element gives the exact description
of the base by its two block conditions.
