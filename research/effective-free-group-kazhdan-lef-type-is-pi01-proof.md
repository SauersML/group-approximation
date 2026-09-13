---
rg: 2
id: effective-free-group-kazhdan-lef-type-is-pi01-proof
kind: route
title: Pi-zero-one measure test, then the free-group ring dichotomy on the measure side and the paradox theorem on the other
target: effective-free-group-kazhdan-lef-type-is-pi01
requires: [effective-subshift-invariant-measure-existence-is-pi01, free-group-crossed-product-matricial-iff-invariant-measure, residually-finite-actions-give-matricial-crossed-products, crossed-products-are-transformation-steinberg-algebras, no-invariant-measure-steinberg-elementary-no-mf-quotient, lef-implies-operator-mf, elementary-groups-over-fg-rings-have-property-t]
artifacts:
  - research/artifacts/un-open-6-tarski-complexity-2026-09-13.md
---

Artifact §2. Fix `e ∈ 𝒫` and write `X = X_e`, `R = R_e`.

1. **Finite generation.** With `u_g χ_Y u_g⁻¹ = χ_(gY)`, the finitely many `χ_{x(1)=a}` (`a ∈ A`) and the `u_s^(±1)`
   (`s` a free generator) generate every cylinder indicator `χ_{x(g)=a} = u_g χ_{x(1)=a} u_g⁻¹` and their products,
   which span `LC(X,F_q)`. So `R` is finitely generated and `elementary-groups-over-fg-rings-have-property-t` gives
   (T) for `EL_N(R)`, `N ≥ 3`.
2. **Measure side.** If `e ∈ P`, `free-group-crossed-product-matricial-iff-invariant-measure` ((i) ⇒ (ii)) makes the
   action residually finite, and `residually-finite-actions-give-matricial-crossed-products` (item 3, `k = F_q`,
   `R` finitely generated) makes every `EL_N(R)`, `N ≥ 3`, LEF.
3. **Paradox side.** If `e ∉ P`, then `R ≅ A_(F_q)(F_r ⋉ X)`
   (`crossed-products-are-transformation-steinberg-algebras`); the transformation groupoid is ample, Hausdorff and
   second countable with compact unit space `X` and no invariant probability measure. So
   `no-invariant-measure-steinberg-elementary-no-mf-quotient` gives `n` with no nontrivial MF quotient of `EL_N(R)`
   for `N ≥ 2n`. Such an `EL_N(R)` is nontrivial and not MF, hence not LEF (`lef-implies-operator-mf`), so item 2 of
   the claim fails.
4. **Arithmetical position.** Items 2 and 3 show that on `𝒫` the LEF-in-every-rank predicate equals `P` and the
   non-MF-from-some-rank predicate equals its complement. `P` is `Π⁰₁` by
   `effective-subshift-invariant-measure-existence-is-pi01`.
