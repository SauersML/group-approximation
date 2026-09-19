---
rg: 2
id: el-r-polynomial-robust-spectral-gap-citation
kind: route
title: Import Dogon–Vigdorovich Corollary 7.7 and the Ershov–Jaikin Kazhdan input
target: el-r-polynomial-robust-spectral-gap
requires: []
artifacts:
  - research/el-r-polynomial-robust-spectral-gap.md
---

# Import Dogon–Vigdorovich Corollary 7.7

LITERATURE INPUT (two items, trust surface explicit):

1. **arXiv:2506.20843v2 (Dogon–Vigdorovich), Corollary 7.7 with
   Proposition 7.6 and Definitions 7.4/7.5.**  Transcribed from the
   PDF by the 2026-08-18 sweep agent:

   > **Definition 7.5.** Let Γ be a finitely presented group, and let
   > 𝒬 be a collection of tracial von Neumann algebras.  We say that Γ
   > satisfies *property (T;𝒬)_rob* if there exist a finite generating
   > set S ⊂ Γ and λ > 0 such that the following holds: For every
   > ε > 0, α > 0 there exists δ > 0 and a finite subset S ⊂ F ⊂ Γ
   > such that for every (M,τ) ∈ 𝒬, and for every (F,δ)-almost
   > representation π: Γ → U(M), the positive operator π(Δ_S) has an
   > (ε,α)-almost λ-spectral gap.

   > **Corollary 7.7.**  (T) ⟹ (T;W*)_rob ⟺ (T;W*) ⟹ (T;CE) ⟺
   > (T;FD)_rob ⟹ (T;FD) ⟹ (τ).

   The (F,δ)-almost representation defect is measured in `‖·‖₂`
   (Def 7.4), which is the norm the downstream application needs.
   The chain was independently re-derived by the sweep from Prop 7.6
   ((T;𝒬)_rob ⟺ (T;𝒫) for 𝒫 the tracial-ultraproduct closure of 𝒬;
   FD-closure = CE, W*-closure = W*) — both the printed and re-derived
   readings agree.  Prop 7.6/Cor 7.7 are stated for finitely
   generated ⟨S⟩, so Def 7.5's "finitely presented" is not consumed.
   §7 has no lattice hypothesis; the lattice-only machinery
   (charmenability, arithmeticity) is confined to §8, not used here.

2. **Ershov–Jaikin-Zapirain: property (T) for
   `EL_r(𝔽_q[x₁…x_d])`, r ≥ 3** — the program's standing Kazhdan
   input for the Kun–Thom pair (same input Kun–Thom's Theorem E
   consumes; already on the program's literature-input surface).

Composition: (2) gives Γ ∈ (T); (1) gives (T) ⟹ (T;FD)_rob; hence Γ
has (T;FD)_rob.  ∎

Residual not imported: the EFFECTIVE Hilbert–Schmidt constants (DV
Rem 7.11 asserts an HS version of Bader's effective Thm 7.10 without
proof).  Only the qualitative statement is certified by this route.
