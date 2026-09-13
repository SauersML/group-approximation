---
rg: 2
id: sl3z-cocompact-quotient-admits-no-topological-microstates
kind: claim
title: For some cocompact Λ, no finite almost-action of SL3(Z) maps almost equivariantly into SL3(R)/Λ
distinct_from:
  sl3z-on-cocompact-lattice-quotient-is-not-sofic: that is measure-theoretic soficity of the action with Haar measure; this is the topological microstate statement, with no measure and no freeness, equivalent to it by unique ergodicity
  sl3-prime-coset-action-exact-atlas-firewall: that excludes exact finite-action atlases for the discrete building-vertex action of SL3(Z[1/2]); this concerns almost-actions of SL3(Z) marked in a compact homogeneous space where approximate equality of marks is metric
---

**OPEN (two-sided).** There are a cocompact lattice `Λ <= SL_3(R)`, a finite `F ⊆ SL_3(Z)` containing
`1`, and `ε > 0` with the following property. There is no finite set `V` with maps
`σ : F → Sym(V)` and `y : V → SL_3(R)/Λ` such that
`|{v : σ(s)σ(t)v != σ(st)v}| <= ε|V|` for `s, t, st ∈ F`, and
`|{v : d(y(σ(s)v), s·y(v)) >= ε}| <= ε|V|` for `s ∈ F`.

**Equivalence.** `SL_3(Z) ↷ SL_3(R)/Λ` is uniquely ergodic
(`sl3z-cocompact-quotient-uniquely-ergodic-minimal`). By
`uniquely-ergodic-action-sofic-iff-topological-microstates`, this claim for `Λ` is equivalent to
nonsoficity of the action on `SL_3(R)/Λ`. Any family of microstates equidistributes to Haar measure
automatically, so a positive construction needs no counting and a negative proof may use any finite
almost-action.

**Calibration.** For `Λ = SL_3(Z)` the space is not compact, so the statement does not apply literally.
But the Hecke orbits there are microstates with `σ` an honest action and `y` exactly equivariant
(`sl3z-lattice-space-action-is-sofic`). For cocompact `Λ` every orbit is infinite, so no microstate can
have `y` exactly equivariant on an honest finite action.

## Attempts

* **Snapping Hecke points.** Move the problem to the dual action of `Λ` on the space of unimodular
  lattices and use matchings of equidistributed finite sets. Dies at: matchings for `λ`, `λ'` and
  `λλ'` agree only metrically, not as permutations (problem node, "Snapping").
* **Discreteness of the labels (live, negative angle).** Lift marks to a compact fundamental domain
  `F_Λ`, `y(v) = g_vΛ`. Below a scale `ε_0(F, F_Λ)`, each good edge `v → σ(s)v` determines a unique
  `λ(v,s) ∈ Λ` with `g_(σ(s)v) ≈ s g_v λ(v,s)`. Around every relator cycle whose vertices are all good,
  the product of the labels is close to `1`, hence equal to `1`. So a microstate is an almost-action of
  `SL_3(Z)` on `V × Λ` that commutes with right `Λ`-translation, with an almost-equivariant bi-map to
  `SL_3(R)`: a discretized measure-equivalence coupling. On an honest finite action with no bad
  vertices, the holonomy is a homomorphism from a finite-index subgroup of `SL_3(Z)` into `Λ`. Landed as
  `sl3z-cocompact-microstates-carry-flat-lambda-labels`. Norm drift
  (`sl3-norm-drift-excludes-finite-almost-invariant-configs`) makes finite labelled orbits cost a fixed
  fraction of defects. With Bass--Milnor--Serre this gives
  `sl3z-cocompact-quotient-uniformly-far-from-finite-actions`: no honest finite action carries
  defect-free marks below a uniform scale. Dies at: microstates may have a vanishing proportion of
  defects and relator failures, and holonomy along loops through them is unconstrained. The missing
  input is a defect-tolerant superrigidity for `Λ`-valued almost-cocycles (part 2 artifact, Section 4).
* **Spectral separation.** Hope: the Koopman representation separates `Λ` from the commensurability
  class of `SL_3(Z)`. Dies at: weak containment of representations is too coarse. Under Jacquet--Langlands
  transfer, the real components of `L^2(SL_3(R)/Λ)` recur in `L^2(SL_3(R)/Γ(N))` for suitable `N`
  (heuristic; transfer not imported).
