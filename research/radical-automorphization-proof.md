---
rg: 2
id: radical-automorphization-proof
kind: route
title: Repeated universal factorization through a radical-kernel self-surjection
target: radical-automorphization
requires: []
artifacts:
  - research/artifacts/radical-renormalization-2026-08-23.md
  - GroupApproximation/Sofic/UniversalFactorization.lean
---

Fix an MF-target homomorphism `phi:G->H`.  Since `ker R <= Rad_MF(G) <= ker
phi`, surjectivity of `R` gives a unique `phi_1:G->H` with
`phi=phi_1 o R`.  The same radical-kernel inclusion applies to `phi_1`, so
iterate to obtain `phi=phi_n o R^n` for every `n`.  Hence `ker(R^n)<=ker phi`
for all `n`; intersect over all MF-target maps to get the stable-kernel
inclusion.

Equivalently, `UniversalFactorization.coronaMFResidual_eq_comap` applied to
the self-surjection says `Rad_MF(G)=R^{-1}(Rad_MF(G))`, and iteration gives the
same conclusion.  Removing the stable kernel makes `R` injective as well as
surjective.  Any quotient through which `R` descends and becomes injective must
kill every `ker(R^n)`, so this quotient is maximal among such quotients.  Finally
the existing exact-quotient criterion gives equality with the MF radical
whenever the automorphization quotient is MF.
