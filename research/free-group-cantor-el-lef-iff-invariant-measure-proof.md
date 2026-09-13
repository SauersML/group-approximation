---
rg: 2
id: free-group-cantor-el-lef-iff-invariant-measure-proof
kind: route
title: Uniform Steinberg simplicity, Kerr–Nowak towers on the measure side, and the groupoid Tarski obstruction on the measure-free side give the free-group Cantor dichotomy
target: free-group-cantor-elementary-group-lef-iff-invariant-measure
requires:
  - crossed-products-are-transformation-steinberg-algebras
  - steinberg-elementary-groups-are-simple-mod-centre
  - elementary-groups-over-fg-rings-have-property-t
  - free-group-crossed-product-matricial-iff-invariant-measure
  - kerr-nowak-measure-free-group-actions-are-rf
  - residually-finite-actions-give-matricial-crossed-products
  - no-invariant-measure-steinberg-elementary-no-mf-quotient
  - stably-infinite-ring-elementary-groups-have-no-mf-quotient
  - lef-implies-operator-mf
artifacts:
  - research/artifacts/un-blueprint-2026-09-13-part1.md
---

**Scope.**
- `F_r`, with `2 <= r < ∞`, acts minimally and topologically freely on the Cantor set `X`.
- `q` is a prime power, and `R = LC(X, F_q) ⋊ F_r` is finitely generated as a ring (for instance, the action is
  expansive).
- For `N >= 3`, `S_N = EL_N(R)/Z(EL_N(R))`.
- The coefficient field is finite. That is needed for finite generation and (T), and it is all this route claims.

**Review status of the inputs.** These passed independent review:
- simplicity: un-verify part 1, 171f0f7525;
- the ring and groupoid no-MF-quotient theorems: part 3, f15928d5c9;
- the two measure-side nodes and the Kerr–Nowak import: un-verify-measure, 10083fd646.

The assembly below is un-architect's and is unreviewed.

**Step 0: structure.**
- `R ≅ A_(F_q)(X ⋊ F_r)` (`crossed-products-are-transformation-steinberg-algebras`).
- The transformation groupoid is Hausdorff and ample. It is minimal because the action is, and effective because the
  action is topologically free. Its unit space `X` is compact and infinite.
- By `steinberg-elementary-groups-are-simple-mod-centre`, every normal subgroup of `EL_N(R)` is central or everything,
  and `Z(EL_N(R)) ⊆ F_q^x I_N`. So `S_N` is infinite and simple.
- `F_q` is finite and `R` is finitely generated, so `S_N` is finitely generated. It has property (T) (third bullet of
  that node, and `elementary-groups-over-fg-rings-have-property-t`).

**Step 1: invariant measure ⇒ `S_N` LEF for every `N >= 3`.**
- **Towers.** An `F_r`-invariant Borel probability measure makes the action residually finite
  (`free-group-crossed-product-matricial-iff-invariant-measure`, (i)⇒(ii), via `kerr-nowak-measure-free-group-actions-are-rf`).
- **The model.** `residually-finite-actions-give-matricial-crossed-products`, item 2, gives an injective unital
  `F_q`-linear ring homomorphism `Ψ : R -> ∏_ω M_(N_n)(F_q)`. It induces an injective homomorphism
  `GL_N(R) -> ∏_ω GL_(N N_n)(F_q)`, and `Ψ(λ I_N) = λ I` for `λ ∈ F_q^x`.
- **The central quotient.** Put `Λ = F_q^x`, a finite group.
  - `∏_ω (GL_(N N_n)(F_q)/Λ I) ≅ (∏_ω GL_(N N_n)(F_q))/[Λ I]`, because `Λ` is finite: an ω-sequence of scalars is
    ω-constant.
  - Let `g ∈ EL_N(R)` with `Ψ(g) ∈ [Λ I]`. Then `Ψ(g) = Ψ(λ I_N)` for some `λ`, so `g = λ I_N`, which is central in
    `EL_N(R)`.
  - Conversely `Z(EL_N(R)) ⊆ Λ I_N` (Step 0).
  - So `S_N` embeds in the ultraproduct of the finite groups `GL_(N N_n)(F_q)/Λ I`.
- **LEF.** A finitely generated subgroup of an algebraic ultraproduct of finite groups is LEF: any finite window of
  products and inequalities holds in ω-many coordinates. So `S_N` is LEF.

**Step 2: no invariant measure ⇒ no MF quotient from rank `2n`, and not LEF.**
- `X` is second countable and `F_q` is countable. By `no-invariant-measure-steinberg-elementary-no-mf-quotient`,
  which feeds the ring theorem `stably-infinite-ring-elementary-groups-have-no-mf-quotient` from `2n[1] <= n[1]` in
  `V(R)`, there is `n >= 1` such that every homomorphism from `EL_N(R)` to an MF group is trivial for `N >= 2n`.
- A homomorphism from `S_N` pulls back along `EL_N(R) -> S_N`, so it is trivial too.
- `S_N` is nontrivial, so it is not MF: the identity is a nontrivial homomorphism into itself.
- So `S_N` is not LEF (`lef-implies-operator-mf`).

**Conclusion.** Every `S_N` (`N >= 3`) is an infinite, finitely generated, simple Kazhdan group.
- If `X` carries an invariant probability measure, `S_N` is LEF for all `N >= 3`.
- Otherwise there is `n` such that every homomorphism from `S_N` to an MF group is trivial for `N >= 2n`, and those
  `S_N` are not LEF.
- Hence `S_N` is LEF for every `N >= 3` iff an invariant probability measure exists.
- **Not covered:** the band `3 <= N < 2n` in the measure-free case (`el-n-mf-quotient-below-twice-paradoxical-level-exists`),
  and crossed products that are not finitely generated.
