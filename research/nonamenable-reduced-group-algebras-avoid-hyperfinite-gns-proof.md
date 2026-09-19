---
rg: 2
id: nonamenable-reduced-group-algebras-avoid-hyperfinite-gns-proof
kind: route
title: A finite injective GNS closure makes the representation Bekka-amenable, and Fell absorption finishes
target: nonamenable-reduced-group-algebras-avoid-hyperfinite-gns
requires: []
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `τ` be a tracial state on `C*_r(Γ)` with GNS representation `π` on
`H_τ` and suppose `N = π(C*_r(Γ))'' = π(Γ)''` is injective.  `N` is finite
(it carries the faithful normal trace induced by `τ`), so injectivity gives
a conditional expectation `Φ : B(H_τ) → N`, and `τ_N ∘ Φ` is a state on
`B(H_τ)` invariant under `Ad(π(g))` for every `g` (`Φ` is an `N`-bimodule
map, `τ_N` is a trace).  So the unitary representation `π` of `Γ` is
amenable in Bekka's sense (M. E. B. Bekka, *Amenable unitary
representations of locally compact groups*, Invent. Math. 100 (1990)), and
by Bekka's characterisation `1_Γ ≺ π ⊗ π̄`.

Since `τ` is a state on the reduced algebra, `π` factors through
`C*_r(Γ)`, i.e. `π ≺ λ_Γ`.  Then
`1_Γ ≺ π ⊗ π̄ ≺ λ_Γ ⊗ λ̄_Γ ≅ (dim ℓ²Γ) · λ_Γ`
by Fell absorption, so `1_Γ ≺ λ_Γ`, which is Hulanicki's characterisation
of amenability of `Γ`.  Contradiction.

For the embedding statement: if `ι : C*_r(Γ) → R` is a unital embedding,
then `τ_R ∘ ι` is a tracial state on `C*_r(Γ)` (faithful, though this is
not needed) whose GNS closure is a von Neumann subalgebra of `R`, hence
injective.
