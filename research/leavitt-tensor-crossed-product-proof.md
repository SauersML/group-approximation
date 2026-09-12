---
rg: 2
id: leavitt-tensor-crossed-product-proof
kind: route
title: Units of degree e_j - e_(j+1) split the Z^d-grading into Z^(d-1) crossed by the last factor
target: leavitt-tensor-powers-are-twisted-crossed-products
requires: []
artifacts:
  - research/artifacts/leavitt-tensor-crossed-product-2026-09-12.md
---

Notation:
- `L = L_k(1,2)`, with `y_i x_j = δ_ij` and `x_1 y_1 + x_2 y_2 = 1`;
- `A = L^(⊗d)`, strongly `Z^d`-graded with `A_v = L_(v_1) ⊗ ... ⊗ L_(v_d)`.

**Step 1 (units).** In positions `j, j+1` put `u_j = Σ_i x_i ⊗ y_i` and
`u_j' = Σ_i y_i ⊗ x_i`. Then:
- `u_j u_j' = Σ_(i,l) x_i y_l ⊗ y_i x_l = Σ_i x_i y_i ⊗ 1 = 1`;
- `u_j' u_j = Σ_(i,l) y_i x_l ⊗ x_i y_l = 1 ⊗ Σ_i x_i y_i = 1`.

So `u_j` is a unit, homogeneous of degree `e_j − e_(j+1)`. The `e_j − e_(j+1)`
form a basis of `Λ = {v : Σ v_i = 0}`. For `λ = Σ_j m_j (e_j − e_(j+1))`,
`u^λ = u_1^(m_1) ⋯ u_(d−1)^(m_(d−1))` is a unit of degree `λ`.

**Step 2 (decomposition).** Put `C = ⊕_(c ∈ Z) A_(c e_d) = L_0^(⊗(d−1)) ⊗ L`.
- Every `v ∈ Z^d` is uniquely `λ + c e_d`, with `c = Σ_i v_i` and
  `λ = v − c e_d ∈ Λ`.
- Since `u^λ` is a unit of degree `λ`, `(u^λ)^(−1) A_v ⊆ A_(c e_d)`, so
  `A_v = u^λ A_(c e_d)`.
- Summing over `v` gives `A = ⊕_(λ ∈ Λ) u^λ C`. The summands are distinct
  `Z^d`-homogeneous pieces, so the sum is direct.

**Step 3 (crossed product data).**
- **Invariance.** Conjugation by a homogeneous unit preserves degrees, so
  `u^λ C (u^λ)^(−1) = C`. Put `α_λ = Ad(u^λ)|_C`.
- **Cocycle.** `ω(λ, μ) = u^λ u^μ (u^(λ+μ))^(−1)` is a unit of degree `0`, and
  `A_0 = L_0^(⊗d) ⊆ C`.
- **Multiplication.**
  `(u^λ c)(u^μ c') = u^λ u^μ α_μ^(−1)(c) c' = ω(λ, μ) u^(λ+μ) α_μ^(−1)(c) c'`.

This is a crossed product `C ∗ Λ`.

**Step 4 (cyclic sub-crossed products).** For `H = Zh ≤ Λ` put `t = u^h`. Then
`u^(mh) ∈ t^m C^x`, so `C ∗ H = ⊕_(m ∈ Z) t^m C = C[t, t^(−1); Ad t]`.

**Step 5 (the two examples).**
- For `h = e_(d−1) − e_d`, `C ∗ H` is spanned by the degrees
  `(0, ..., 0, a, c − a)`. It is `L_0^(⊗(d−2)) ⊗ L ⊗ L`.
- For `h = e_1 − e_2`, it contains `(⊕_n L_n ⊗ L_(−n)) ⊗ 1^(⊗(d−2))`, the
  Bernoulli crossed product of `leavitt-tensor-powers-not-left-coherent-proof`
  Step 2, tensored with the identity.

The non-commutation example `u_1 u_2 ≠ u_2 u_1` for `d = 3` is computed in the
artifact, Section 2.
