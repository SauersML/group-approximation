---
rg: 2
id: unit-abelianization-algebraic-k1-gap-proof
kind: route
title: Polar decomposition turns the component group into a quotient of the unit group
target: unit-abelianization-to-algebraic-k1-not-injective
requires:
  - simple-ah-witness-is-elementary-in-rank-two
  - stw59-simple-ah-non-k1-injective
artifacts:
  - research/artifacts/ah-k1-mf-bridge-2026-09-07.md
---

## Why sufficient

**Zero on the right.**  `simple-ah-witness-is-elementary-in-rank-two` gives
`diag(v,1_A) in E_2(A)`, so the class of `v` in
`K_1^alg(A) = GL_infinity(A)/E_infinity(A)` is zero.

**Nonzero on the left.**  Polar decomposition retracts `A^x` onto `U(A)` and
is a homotopy equivalence, so `pi_0(A^x) = pi_0(U(A)) = U(A)/U_0(A)`.  The
quotient map `A^x -> pi_0(A^x)` is a group homomorphism, since `A^x` is a
topological group and the identity component is normal, so it kills every
commutator and factors through `(A^x)^ab`.  By
`stw59-simple-ah-non-k1-injective`, `v` is not in `U_0(A)`, so its image in
`pi_0(A^x)` is nontrivial, and its class in `(A^x)^ab` is therefore
nontrivial.
