---
rg: 2
id: virtually-free-cantor-el-lef-iff-invariant-measure-proof
kind: route
title: Uniform Steinberg simplicity, the virtually free measure-matricial equivalence, and the groupoid Tarski obstruction give the virtually free Cantor dichotomy
target: virtually-free-cantor-elementary-group-lef-iff-invariant-measure
requires:
  - crossed-products-are-transformation-steinberg-algebras
  - steinberg-elementary-groups-are-simple-mod-centre
  - elementary-groups-over-fg-rings-have-property-t
  - elementary-group-fg-from-fg-coefficient-ring
  - virtually-free-crossed-product-matricial-iff-invariant-measure
  - residually-finite-actions-give-matricial-crossed-products
  - no-invariant-measure-steinberg-elementary-no-mf-quotient
  - stably-infinite-ring-elementary-groups-have-no-mf-quotient
  - lef-implies-operator-mf
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part1.md
---

Modelled on `free-group-cantor-el-lef-iff-invariant-measure-proof`; only Step 1's source of towers changes.

**Scope.**
- `Γ` is a virtually free group acting minimally and topologically freely on the Cantor set `X`.
- `q` is a prime power, and `R = LC(X, F_q) ⋊ Γ` is finitely generated as a ring. This forces `Γ` to be finitely
  generated, and holds for instance for expansive actions.
- For `N >= 3`, `S_N = EL_N(R)/Z(EL_N(R))`.
- The coefficient field is finite. That is needed for finite generation and (T), and it is all this route claims.

**Review status of the inputs.**
- simplicity: un-verify part 1, 171f0f7525;
- the ring and groupoid no-MF-quotient theorems: un-verify part 3, f15928d5c9;
- Theorem A (residual finiteness gives matricial models): un-verify-measure, 10083fd646;
- the virtually free measure–RF–matricial equivalence, with finite-index induction and co-induction: un-verify-measure part 5, 97bf4bc468.

The assembly below is this lane's and is unreviewed.

**Step 0: structure.**
- `R ≅ A_(F_q)(X ⋊ Γ)` (`crossed-products-are-transformation-steinberg-algebras`).
- The transformation groupoid is Hausdorff and ample. It is minimal because the action is, and effective because the
  action is topologically free. Its unit space `X` is compact and infinite.
- By `steinberg-elementary-groups-are-simple-mod-centre`, every normal subgroup of `EL_N(R)` is central or everything,
  and `Z(EL_N(R)) ⊆ F_q^x I_N`. So `S_N` is infinite and simple.
- `R` is finitely generated, so `EL_N(R)` is finitely generated (`elementary-group-fg-from-fg-coefficient-ring`) and has
  property (T) (`elementary-groups-over-fg-rings-have-property-t`); so does its quotient `S_N`.

**Step 1: invariant measure ⇒ `S_N` LEF for every `N >= 3`.**
- **Towers.** A `Γ`-invariant Borel probability measure makes the action residually finite and gives an injective
  unital `F_q`-linear `Ψ : R -> ∏_ω M_(N_n)(F_q)` (`virtually-free-crossed-product-matricial-iff-invariant-measure`,
  (i)⇒(ii)⇒(iii), whose map is item 2 of `residually-finite-actions-give-matricial-crossed-products`).
- **The model.** `Ψ` induces an injective homomorphism `GL_N(R) -> ∏_ω GL_(N N_n)(F_q)` with `Ψ(λ I_N) = λ I` for
  `λ ∈ F_q^x`.
- **The central quotient.** Put `Λ = F_q^x`, a finite group.
  - `∏_ω (GL_(N N_n)(F_q)/Λ I) ≅ (∏_ω GL_(N N_n)(F_q))/[Λ I]`, because an ω-sequence of scalars from a finite set is
    ω-constant.
  - If `g ∈ EL_N(R)` and `Ψ(g) ∈ [Λ I]`, then `Ψ(g) = Ψ(λ I_N)` for some `λ`, so `g = λ I_N` by injectivity, which is
    central.
  - Conversely `Z(EL_N(R)) ⊆ Λ I_N` (Step 0). So `S_N` embeds in the ultraproduct of the finite groups
    `GL_(N N_n)(F_q)/Λ I`.
- **LEF.** A finitely generated subgroup of an algebraic ultraproduct of finite groups is LEF: any finite window of
  products and inequalities holds in ω-many coordinates. So `S_N` is LEF.

**Step 2: no invariant measure ⇒ no MF quotient from rank `2n`, and not LEF.**
- `X` is second countable and `F_q` is countable. By `no-invariant-measure-steinberg-elementary-no-mf-quotient`, which
  feeds `stably-infinite-ring-elementary-groups-have-no-mf-quotient` from `2n[1] <= n[1]` in `V(R)`, there is `n >= 1`
  such that every homomorphism from `EL_N(R)` to an MF group is trivial for all `N >= 2n`.
- A homomorphism from `S_N` pulls back along `EL_N(R) -> S_N`, so it is trivial too.
- `S_N` is nontrivial, so it is not MF (the identity would be a nontrivial homomorphism into an MF group), hence not
  LEF (`lef-implies-operator-mf`).

**Conclusion.** Every `S_N` (`N >= 3`) is an infinite, finitely generated, simple Kazhdan group.
- If `X` carries an invariant probability measure, `S_N` is LEF for all `N >= 3`.
- Otherwise there is `n` such that every homomorphism from `S_N` to an MF group is trivial for `N >= 2n`, and those
  `S_N` are not LEF.
- Hence `S_N` is LEF for every `N >= 3` iff an invariant probability measure exists.
- **Not covered:** the band `3 <= N < 2n` in the measure-free case (`el-n-mf-quotient-below-twice-paradoxical-level-exists`),
  crossed products that are not finitely generated, and acting groups that are not virtually free (for groups
  containing `Z^2` the measure-to-towers step fails: `z2-containing-groups-have-non-rf-measure-actions`).
