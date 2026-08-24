---
rg: 2
id: radical-automorphization-proof
kind: route
title: Repeated universal factorization through a radical-kernel self-surjection
target: radical-automorphization
requires: []
artifacts:
  - research/artifacts/radical-renormalization-2026-08-23.md
  - GroupApproximation/Sofic/RadicalAutomorphization.lean
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

Lean carries the whole step in `Sofic/RadicalAutomorphization`.  The engine is
`stableKernel_le_of_comap_le`, whose only hypothesis is `Rad.comap R <= Rad` --
no surjectivity, no target class, no countability -- so the four instantiations
`stableKernel_le_coronaMFResidual`, `stableKernel_le_fdUnitaryResidual`,
`stableKernel_le_finiteResidual` and `stableKernel_le_linearResidual` differ
only in which factorization theorem discharges that inclusion.  Maximality is
the same lemma with the radical replaced by an arbitrary subgroup
(`stableKernel_le_of_injective_descent`), the automorphism is `descendEquiv`,
and the exact form is `coronaMFResidual_eq_stableKernel`.
