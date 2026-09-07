---
rg: 2
id: aut-projective-max-mf-quotient-proof
kind: route
title: Morita invariance moves the classification to every endomorphism ring
target: aut-of-projective-module-max-mf-quotient-is-k1
requires:
  - purely-infinite-unit-group-max-mf-quotient-is-k1
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

## Why sufficient

Put `S = End_R(P)`, so `Aut_R(P) = S^x`.  `S` is Morita equivalent to `R`
because `P` is a nonzero finitely generated projective, and the class of
purely infinite simple rings is closed under Morita equivalence:
Ara--Goodearl--Pardo Corollary 1.7, quoted, "The class of purely infinite
simple rings is closed under Morita equivalence."  `S` is countable because
`R` is and `P` is finitely generated.

Applying `purely-infinite-unit-group-max-mf-quotient-is-k1` to `S` gives
`S^x / Rad_MF(S^x) = K_1(S)`, and `K_1` is Morita invariant, so
`K_1(S) = K_1(R)`.
