---
rg: 2
id: ccr-for-coordinate-collapsing-models
kind: claim
title: Compressor-commutant rigidity holds for every coordinatewise model with image collapse
distinct_from:
  kt-centralizer-normalization-hs: that is the (CCR)/normalization question for ARBITRARY trace-preserving representations into the ultraproduct, which is what the Theorem-A endgame consumes; this is the genuine-coordinate special case, proved, which that node's excess-commutant analysis identified as the first battlefield.
  compressor-coset-two-point-exact: that is the permutation-side residual visibility of compressor COSETS in congruence quotients; this uses the subgroup-IMAGE collapse (π(tΓt⁻¹) = π(Γ), E-normality) on the Hilbert–Schmidt side, and its conclusion is about commutants, not cosets.
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**Theorem.**  Let `Λ ≤ Γ ≤ G` with `Λ` finitely generated with property
(T), and let `σ = ∏_𝒰 π_n : G → U(M)`, `M = ∏_𝒰 (M_{d_n}, tr)`, be a
coordinatewise ultraproduct of genuine finite-dimensional unitary
representations such that `π_n(Γ) ⊆ π_n(Λ)` for 𝒰-most `n`.  Then

```text
σ(Λ)' ∩ M = σ(Γ)' ∩ M .
```

In particular **(CCR) holds for the canonical congruence
representation** of the Kun–Thom pair: for `Λ = tΓt⁻¹` (a strict
compressor of the Kazhdan group `Γ = EL_r(𝔽_q[x₁…x_d])` inside
`G = EL_r(R) ⋊ SL_d(ℤ)`), every congruence quotient collapses the
compression — `π_M(tΓt⁻¹) = π_M(t) E π_M(t)⁻¹ = E = π_M(Γ)` by
normality of the elementary part — so the hypothesis holds along any
congruence chain, and the commutant of the compressed copy equals the
commutant of `Γ` in the sofic ultraproduct.

Proof: `ccr-for-coordinate-collapsing-models-proof` — one application
of the Kazhdan distance-to-invariant-vectors inequality per
coordinate, plus the image containment.  Five lines; no groupoids, no
medians, no atomicity.

**What it changes.**

1. **First positive instance of (CCR).**  The rigidity-side hole
   `kt-centralizer-normalization-hs` asked whether compressing a
   Kazhdan group can grow its relative commutant; for every model
   built from genuine coordinate representations with image collapse
   the answer is NO, exactly.
2. **Congruence models cannot refute the route.**  Any refutation of
   (CCR) — hence any flexible-side comfort from that quarter — must
   use representations with NO genuine coordinate structure: the
   excess-commutant locus (Alekseev–Thom OP 6.2's gap) is now provably
   the ONLY place a counterexample can live.
3. **The remaining distance is sharply named.**  The Theorem-A endgame
   needs (CCR) for the restriction of an arbitrary embedding of
   `L(W)`, i.e. for approximate-coordinate representations.  What is
   missing is exactly an extension of the per-coordinate Kazhdan
   uniformity across the approximate-vs-genuine homomorphism gap —
   not component sizes, not isotropy orders, not any other atomic
   invariant.  The two median arguments of Kun–Thom 4.1 are not
   needed in the collapsing regime at all.

**Fences.**  This does not decide `kt-centralizer-normalization-hs`
(arbitrary `σ` remains open), does not touch
`invariant-cartan-completion`, and selects no branch of
`leavitt-steinberg-hs-unstable`.  The hypothesis `π_n(Γ) ⊆ π_n(Λ)` is
special to collapsing chains: a chain separating `Γ` from `tΓt⁻¹`
coordinatewise (if one exists for some non-congruence family of
finite-dimensional representations) is outside its scope.
