---
rg: 2
id: tree-product-stationary-measures-are-parabolic-averages-proof
kind: route
title: Poisson boundary via Kaimanovich's strip criterion on flats, then the Furstenberg boundary map
target: tree-product-stationary-measures-are-parabolic-averages
requires: []
artifacts:
  - research/artifacts/zp-tree-lattice-left-orderability-2026-09-13-part3.md
---

Direct proof, written in artifact part 3, §§1–4.

1. **Convergence (§1).**
   - `G_i` is non-amenable: a hyperbolic element moves the unique `K_i`-invariant probability on
     `∂T_i`.
   - The symmetric `G`-invariant vertex chain has spectral radius `< 1`, so `P[x_n^i = v] ≤ C ρ^n`.
   - Borel–Cantelli against balls of `D^(cn)` vertices gives linear escape. Bounded increments in a tree
     then force convergence to an end.
   - The hitting law is `K`-invariant, hence the unique `K`-invariant (nonatomic) measure `ν_B` on
     `∂T_1 × ∂T_2`.
2. **Poisson boundary of `(Γ, μ_Γ)` (§2).**
   - Sampling at hitting times of `KΓ` gives the `μ_Γ`-walk (Witte Morris, Definition 5.4) with the same
     limit, and `μ_Γ` has finite first moment (Lemma 5.5).
   - Strips `S(b_-, b_+) = {γ : d(γo, ℓ_1 × ℓ_2) ≤ M}` around the flat spanned by the two geodesic lines
     are `Γ`-equivariant and contain `O(k^2)` elements of word length `≤ k`.
   - Kaimanovich, arXiv:math/9802132v2, Theorem 6.5(a), p. 677, gives maximality.
3. **Harmonic functions on `G` (§3).** Restriction to `Γ` is harmonic (Witte Morris, Remark 5.3). It is a
   Poisson integral over `ν_B`. The Poisson integral on `G` is harmonic and agrees on `Γ`, so by uniqueness
   of harmonic extension (Proposition 5.6, Remark 5.3) the two coincide.
4. **Decomposition (§4).**
   - The positive linear map `φ ↦ F_φ` gives an a.e. equivariant `β : B → Prob(X)` with barycenter `ν`.
     Make it strictly equivariant, using transitivity of `G` on `B = G/P`.
   - Put `λ = β(eP)`, which is `P`-invariant, and use `G = KP`.
   - Uniqueness: any `P`-invariant `λ'` with the same `K`-average defines an equivariant `β'` with
     `E[β'(η(ω)) | ℱ_n] = (x_n)_* ν`. Martingale convergence identifies `β'(η(ω))` with `lim (x_n)_* ν`
     a.s., so `β' = β` and `λ' = λ`.

Statement-level imports, not re-read: the spectral gap for symmetric spread-out measures on non-amenable
lcsc groups (Derriennic–Guivarc'h, Berg–Christensen), and the measurable-selection lemma (Zimmer). Unreviewed.
