---
rg: 2
id: matricial-steinberg-algebras-have-invariant-measures
kind: claim
title: A unital homomorphism of a Steinberg algebra into a matrix ultraproduct yields a groupoid-invariant probability measure on the unit space
distinct_from:
  leavitt-algebra-has-no-unital-rank-model: that is the Leavitt instance in the rank metric; this is the general necessary condition for every Hausdorff ample groupoid with compact unit space.
  amenable-full-group-forces-invariant-measure: that derives a measure from amenability of a full group; this derives one from a matricial model of the coefficient ring.
artifacts:
  - research/artifacts/un-measure-residually-finite-lef-rings-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `𝒢` be a Hausdorff ample groupoid with compact unit space `X`,
`k` a field, and `Ψ : A_k(𝒢) -> ∏_ω M_(N_n)(k)` a unital ring homomorphism, not necessarily injective.
1. `rk(a) = lim_ω rank(ψ_n(a))/N_n` is a unital Sylvester matrix rank function on `A_k(𝒢)`.
2. `μ(U) = rk(1_U)` on clopen `U ⊆ X` extends to a Borel probability measure with
   `μ(s(B)) = μ(r(B))` for every compact open bisection `B`.
3. If `Ψ` is injective, `A_k(𝒢)` is stably finite. If also `k` is finite, every finitely generated
   subgroup of every `GL_m(A_k(𝒢))` is LEF.

**Calibration.** For the Cuntz groupoid (`A = L_k(1,2)`), bisections `B_1, B_2` with `s(B_i) = X` and
`r(B_1) ⊔ r(B_2) = X` force `μ(X) = 2μ(X)`. So no unital `Ψ` exists, as
`leavitt-algebra-has-no-unital-rank-model` also shows.

Route: `matricial-steinberg-algebras-have-invariant-measures-proof`.
