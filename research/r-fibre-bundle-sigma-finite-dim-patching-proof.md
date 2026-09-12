---
rg: 2
id: r-fibre-bundle-sigma-finite-dim-patching-proof
kind: route
title: Lift central matrix units from trivial restrictions, patch two systems by a flip unitary, induct on derived length
target: r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial
requires:
  - r-fibre-bundle-triviality-iff-uniform-central-halving
  - r-fibre-w-star-bundle-finite-dim-base-is-trivial
  - bauer-gamma-failure-localizes-to-infinite-dim-point
artifacts:
  - research/artifacts/w-bundle-sigma-finite-dim-triviality-2026-09-12.md
---

The full argument is in the artifact.

1. **Lifting (Lemma 1).**
   - Suppose `M_Y` is trivial over a closed `Y`.
   - Approximate a finite set `F` uniformly on `Y` by dyadic matrix algebras `D_m`, using Dini's theorem.
   - Take exact matrix units of `M_2 ⊂ D_m' ∩ R` and lift them through the quotient `M → M_Y`.
   - The defect functions `λ ↦ E(z*z)(λ)` are continuous, so the lifted system is δ-good on an open set `O ⊇ Y`.
2. **Patching (Lemma 2).**
   - Take a system `a` good on `O`, and a system `b` good on `C = K ∖ O'` against `F` and the entries `a_ij`.
   - Put `w = Σ a_ij b_ji`, `h = (1 − Re w)/2`, and `u = exp(iπ g h)` with a central Urysohn function `g`.
   - Set `c = (1 − κ) u a u* + κ b`, with a second cutoff `κ`.
   - `c` is `Cδ`-good on all of `K`, where `C` does not depend on `K` or its dimension.
   - The estimate uses `‖u − (1 + (e^{iπs} − 1)h)‖_2 ≤ C‖h² − h‖_2` and the flip identity `w a w ≈ b`.
3. **Induction on derived length.**
   - The length `ℓ(X)` is a successor ordinal, and derived sets of closed subsets are monotone.
   - With `Y = X^(γ)` finite-dimensional, the restriction `M_Y` is trivial by `r-fibre-w-star-bundle-finite-dim-base-is-trivial`.
   - The complement `C = X ∖ O'` has `ℓ(C) ≤ γ`, so `M_C` is trivial by induction.
   - Restrictions to closed sets are strictly separable R-fibre bundles; see `bauer-gamma-failure-localizes-proof`, step 4.
   - Lemmas 1 and 2 give a good system on `X`.
4. **Conclusion.**
   - Extract `p = ((c_11 + c_11*)/2)_+`.
   - Diagonalize over a strictly dense sequence in the unit ball; the strict topology equals the ‖·‖_{2,u} topology on bounded sets.
   - This gives condition (ii) of `r-fibre-bundle-triviality-iff-uniform-central-halving`, hence triviality.
5. **Localization.** For `z ∉ K^(∞)`, a closed neighbourhood disjoint from `K^(∞)` is reducible, so `z ∉ Z(M)`.
6. **Countable unions.** Reducible is equivalent to being a countable union of closed finite-dimensional sets: the forward direction by Baire, the converse by σ-compact strata.
