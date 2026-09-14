---
rg: 2
id: laurent-elements-of-cantor-crossed-products-are-suitable
kind: claim
title: Every Laurent polynomial in u is a suitable (exchange) element of LC(X,F) ⋊ Z for a minimal Cantor system, with the idempotent in a tower algebra
distinct_from:
  minimal-cantor-crossed-product-is-an-exchange-ring: that asks for the exchange property of every element of the ring; this proves it for the Laurent polynomials in u, the centralizer of u.
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `(X,T)` be a minimal homeomorphism of the Cantor set, `F` a field, and `R = LC(X,F) ⋊_T Z`. For every `p ∈ F[u^{±1}]` there is an idempotent `e ∈ R` with `e ∈ pR` and `1 − e ∈ (1−p)R`.

The idempotent can be chosen in a tower algebra `A_𝒫 ≅ ∏_a M_{h_a}(F)` of a Kakutani–Rokhlin partition with heights `≥ deg p_0 + deg r_0`, where `p = u^αp_0` and `1−p = u^βr_0` with `p_0(0), r_0(0) ≠ 0`.

**Contrast.** In `F_2[u^{±1}]` the element `u + u²` is not suitable, since the only idempotents there are `0` and `1`. In `R` it is.

**Proof outline.**
- On a block `F^h` the residue map `δ_i ↦ (ū^i, ū^i) ∈ F[u]/(p_0) × F[u]/(r_0) ≅ F[u]/(p_0r_0)` is onto.
- The projection `E_h` onto the preimage of `0 × F[u]/(r_0)`, along the kernel plus the preimage of the first factor, kills the first residue and fixes the second.
- Glued over tower occurrences, `e = ⊕E_h` satisfies `ρ_p∘e = 0` and `ρ_{1−p}∘(1−e) = 0`, because the residues are covariant under translation by the unit `ū^b`.
- `laurent-right-ideals-of-cantor-crossed-products-columnwise` turns these into `e ∈ pR` and `1−e ∈ (1−p)R`.
