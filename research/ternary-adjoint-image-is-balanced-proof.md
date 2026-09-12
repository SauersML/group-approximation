---
rg: 2
id: ternary-adjoint-image-is-balanced-proof
kind: route
title: Both multiplications send g (x) g^-1 to 1, and scalar values multiply
target: ternary-adjoint-image-is-balanced
requires: []
artifacts:
  - research/artifacts/klein-target-balanced-invariant-2026-09-12.md
---

`mu(g (x) g^-1) = g g^-1 = 1 = g^-1 g = mu'(g (x) g^-1)`, and both maps are linear. For
`T = sum a_i (x) b_i^op` and `T' = sum a'_j (x) b'_j^op`, `TT' = sum a_i a'_j (x) (b'_j b_i)^op`, so
`mu(TT') = mu(T') mu(T)` and `mu'(TT') = mu'(T) mu'(T')` whenever those values are scalars.
Theorem 1 and Lemma 2 of the artifact.
