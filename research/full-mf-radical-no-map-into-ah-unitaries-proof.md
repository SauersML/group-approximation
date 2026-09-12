---
rg: 2
id: full-mf-radical-no-map-into-ah-unitaries-proof
kind: route
title: The image is a countable subgroup of the unitaries of an MF algebra
target: full-mf-radical-group-has-no-map-into-ah-unitaries
requires:
  - mf-approximation-does-not-give-k1-injectivity
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

## Why sufficient

Let `phi : H -> U(A)`.  Its image is a countable subgroup of `U(A)`, and by
the prerequisite `A` is MF, so every countable subgroup of `U(A)` is an MF
group.  So `phi` is a homomorphism from `H` to an MF group, and
`Res_MF(H) = H` makes it trivial.
