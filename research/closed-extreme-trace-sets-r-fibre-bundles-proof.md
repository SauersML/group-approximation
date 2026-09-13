---
rg: 2
id: closed-extreme-trace-sets-r-fibre-bundles-proof
kind: route
title: Choquet uniqueness makes the hull a Bauer face; Ozawa's Section 5 makes its completion a W*-bundle
target: closed-extreme-trace-sets-give-r-fibre-w-star-bundles
requires: []
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

Direct proof with verbatim literature imports: Section 1 of the artifact.

1. **Face (Lemma 1).**
   - `conv‾(K)` is the set of barycentres of `Prob(K)`, and Milman's converse gives
     `∂_e F = K`.
   - For the face property: if `τ = tτ' + (1−t)τ''` lies in `F`, the measure
     `tμ_{τ'} + (1−t)μ_{τ''}` is maximal and represents `τ`.
   - Uniqueness of maximal measures in a Choquet simplex identifies it with a measure
     on `K`. So `μ_{τ'}` is carried by `K`, and `τ' ∈ F`.
2. **Bundle (Proposition 2).**
   - Ozawa, arXiv:1304.3523, works with "a non-empty metrizable closed face" `S`
     (MSI copy, line 114).
   - Lines 766–770: "it is a continuous W*-bundle over ∂S if ∂S is closed in S".
   - Theorem 3: "if ∂S is closed, then for every τ ∈ ∂S, one has π_τ(A^st) = π_τ(N) = π_τ(A)''".
   - The introduction gives `A^u = A^st`.
   - Nuclearity and the absence of finite-dimensional representations make each factor
     `π_λ(A)''` an injective II_1 factor, hence `R` (Connes).
3. **Dictionary (Lemma 3).** Constant sections give a unital `M_N ⊂ M_K`. Write `M_K`
   as the bounded Cauchy sequences modulo the null sequences. Projectivity of the cone
   over `M_N` lifts this to order zero maps `ψ_m: M_N → A`, with
   `λ(1 − ψ_m(1)) ≤ ‖1 − ψ_m(1)‖_{2,F} → 0` uniformly on `K`.
