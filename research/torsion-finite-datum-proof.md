---
rg: 2
id: torsion-finite-datum-proof
kind: route
title: The truncated relator set is still inside R, so the torsion element stays nontrivial
target: torsion-is-a-finite-datum-torsion-freeness-is-not
requires: []
artifacts:
  - research/artifacts/torsion-free-transfer-covers-and-obstructions-2026-09-08.md
---

## Proof

Order the finite subsets of `R` by inclusion and let `R_i` be the normal
closure in `F` of the `i`-th one; then `R_i <= R_(i+1)`, each `F/R_i` is
finitely presented, and `union_i R_i = R` because every element of `R` lies in
one of the finite subsets.

Since `w^m in R = union_i R_i` and the union is increasing, `w^m in R_i` for
all large `i`.  Fix such an `i`.  In `F/R_i` the image of `w` satisfies
`(w R_i)^m = w^m R_i = R_i`, so it has order dividing `m`.  It is nontrivial:
`w R_i = R_i` would give `w in R_i <= R`, contradicting `(TF1)`.

Hence the image of `w` is a nontrivial element of order dividing `m` in the
finitely presented group `F/R_i`.
