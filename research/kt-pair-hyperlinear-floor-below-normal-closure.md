---
rg: 2
id: kt-pair-hyperlinear-floor-below-normal-closure
kind: claim
title: For the Theorem E pair some coset wreath over an intermediate subgroup not containing the normal closure is hyperlinear
distinct_from:
  hyperlinear-wreath-model: that is the single case Δ = Γ; this asks for any Δ with Γ ≤ Δ and ⟨⟨Γ⟩⟩ ⊄ Δ, a disjunction strictly implied by it
  theorem-c-separation-iff-infranormal-coset-wreath: that is the general equivalence; this is its open instance for the explicit Kun--Thom pair
  kt-intermediate-coset-wreaths-are-nonsofic: that proves every such W_Δ is nonsofic; this asks for one of them to be hyperlinear
  kt-hyperlinear-coset-wreath-forces-nonroundable-vertex: that derives HS-instability consequences from a hyperlinear W_K; this is the existence question itself, recast as the only Theorem-C route to a hyperlinear nonsofic action
---

**OPEN.** Let `Γ = EL_r(F_q[x_1,…,x_d]) < G = EL_r(F_q[x_1^(±1),…,x_d^(±1)]) ⋊ SL_d(Z)`,
`r,d ≥ 3` (Kun--Thom Theorem E). There is a subgroup `Δ` with `Γ ≤ Δ ≤ G` and
`⟨⟨Γ⟩⟩ ⊄ Δ` such that `W_Δ = (⊕_(G/Δ) Z/2) ⋊ G` is hyperlinear. Equivalently
(`theorem-c-separation-iff-infranormal-coset-wreath`) the hyperlinear floor
`Δ_hl(Γ,G)` does not contain `⟨⟨Γ⟩⟩`, and then one may take `Δ = Δ_hl`, which is
infranormal and not normal.

This is implied by `hyperlinear-wreath-model` (`Δ = Γ`) and is equivalent to the
existence of any hyperlinear `G`-action whose `Γ`-fixed algebra is not `G`-invariant.
Only infranormal non-normal `Δ ⊇ Γ` need be searched. For `[Δ:Γ] < ∞` the wreath `W_Δ`
embeds in `W_Γ`, so the new cases are the infinite-index infranormal overgroups of `Γ`
that do not contain the normal closure.

A positive answer also gives a hyperlinear nonsofic **group**, since `W_Δ` is nonsofic by
`kt-intermediate-coset-wreaths-are-nonsofic`. So, for this pair, the Theorem-C route to a
hyperlinear nonsofic action costs exactly as much as the Pestov-level separation for the
groups `W_Δ`; the action version brings no discount.

## Progress (2026-09-17): the explicit candidates collapse to Δ = Γ

* **Where Δ_hl can live.** `Δ_hl` is stable under `Mon = SL_d(Z) ∩ M_d(N) ⊆ P_Γ`. If this
  node holds, `Δ_hl` meets every root subgroup exactly in its polynomial part,
  `e_ij(f) ∈ Δ_hl ⇔ f ∈ A`, and `π(Δ_hl)` is `{1}`, `{±I}` or Zariski dense
  (`kt-compressor-stable-overgroups-have-polynomial-content`). So no
  hyperlinear floor below the normal closure can enlarge the elementary content, for
  example to `F_q[M]` with `M` a proper monoid.
* **HNN and monomial-split candidates give nothing new.** For any hyperlinear `W_Δ`
  with `Δ ⊇ Γ`, the compressor core `∩_(P∈Mon) P^(-1)ΔP` is again hyperlinear. For
  `Δ = E_r(F_q[M]) ⋊ Q` with `N^d ⊆ M ≠ Z^d`, that core is `Γ`. This covers every
  one-compressor ascending HNN `⟨Γ,t⟩` (`t ∈ Mon`) and every half-space monoid. A
  hyperlinear wreath over one of these forces `hyperlinear-wreath-model`
  (`kt-monomial-split-coset-wreaths-collapse-to-gamma`).
* **Residual gap.** Non-split `Mon`-stable overgroups of `Γ` with polynomial elementary
  content remain. If there are none
  (`kt-compressor-stable-polynomial-content-overgroups-are-gamma`), this node is
  equivalent to `hyperlinear-wreath-model`
  (`kt-pair-floor-reduces-to-wreath-model-via-compressor-sandwich`). Otherwise such
  counterexamples are the only remaining candidates for Δ.

## Attempts

* **Reduced to `hyperlinear-wreath-model`, both directions (w6-121).** With the compressor
  sandwich proved (`kt-kernel-overgroups-polynomial-via-vertex-compressors-proof`), the
  per-model saturation zero-one law `kt-gamma-saturation-is-gamma-or-contains-e` holds: for
  every homomorphism `π` of `G` into any group, the bicommutant saturation `Γ^sat(π)` is `Γ`
  or contains `E`. Hence the floor `K_Γ = Δ_hl ∩ E` is `Γ` or `E`, and this node holds iff
  `W_Γ` is hyperlinear. The residual candidates of the Progress section (non-split
  `Mon`-stable overgroups) do not exist, and no `Δ` with `Γ < Δ`, `E ⊄ Δ` gives anything that
  `Δ = Γ` does not. The node is now as hard as `hyperlinear-wreath-model` and no easier;
  the sharpest form of both is the single-enemy criterion (Corollary 3 there): one
  canonical CE model of the residually finite group `G` with one `Γ`-central element that
  fails to commute with `σ(e_12(x_1^(-1)))`.
