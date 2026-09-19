---
rg: 2
id: diagonal-normalizer-rigidity-proof
kind: route
title: Doubly stochastic rigidity plus untwisting and free amplification
target: diagonal-normalizer-rigidity
requires: []
artifacts:
  - notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md
---

# Doubly stochastic rigidity plus untwisting and free amplification

Direct establishment; the complete argument is Lemmas 3–5, Theorem 6 and
Corollaries 7–8 of the cited note. `requires: []` is a proof commitment.

The three moves:

1. **Doubly stochastic rigidity.** For `u ∈ U(N)` and real diagonal `f`, the
   diagonal part of `u f u*` is `Af` for the doubly stochastic
   `A_ij = |u_ij|²`. Since `E_(D_N)` is the `‖·‖₂`-orthogonal projection and
   `u(·)u*` is a `‖·‖₂`-isometry, the defect is exactly
   `‖f‖₂² − ‖Af‖₂²`. Averaging over `f ∈ {−1,1}^N` — all of them contractions
   in `D_N` — gives `(1/N)Σ_ij A_ij² ≥ 1 − δ²`. Rows of `A` are probability
   vectors, so `Σ_j A_ij² ≤ max_j A_ij ≤ 1`, and Markov produces `(1−δ)N`
   rows with a column of mass `≥ 1 − δ`. Column sums equal `1`, so all but
   `2δN` of those choices are already injective; complete to a permutation
   and read off the phases. This is the finite-dimensional statement, with a
   constant independent of `N`, so it survives the ultraproduct verbatim: the
   supremum in the defect is attained by compactness, so a sequence violating
   it would give a single element of `D_𝒰` moved out of `D_𝒰`.

2. **Untwisting.** Factor `Θ(u_g) = s_g c_g` uniquely in `𝒮_𝒰 ⋉ U(D_𝒰)`.
   Uniqueness makes `g ↦ s_g` a homomorphism, and `c_g` commutes with
   `Θ(L^∞(X)) ⊆ D_𝒰` because `D_𝒰` is abelian, so `s_g` alone implements the
   action. This is the point where the abelianness of the base is consumed.

3. **Free amplification.** `s` need not satisfy `tr(s_g) = 0`, so
   `f u_g ↦ Θ(f)s_g` need not preserve the trace. Tensor with a free sofic
   representation `σ` of `G` on `Y'_n`: `ŝ_g = s_g ⊗ σ_g` is a permutation of
   `Y_n × Y'_n`, still implements the action on `Θ(L^∞(X)) ⊗ 1 ⊆ D̂_𝒰`, and
   `tr(Θ(f)s_g)·tr(σ_g) = 0` for `g ≠ 1`. This is the standard
   trace-amplification device, and it is where soficity of `G` (residual
   finiteness, Kun–Thom Theorem E) is used.

Combining with `coordinate-action-not-sofic` (Kun–Thom Corollary D) gives the
sharpened form of the boundary: for the Kun–Thom pair no embedding of `M_KT`
can have the Bernoulli algebra in a diagonal ultraproduct **and** the group
unitaries in its normalizer. Since the first half is always arrangeable
(the diagonalization lemma of `notes/NOTEPAD.md`), the second half is the
whole of the remaining question.
