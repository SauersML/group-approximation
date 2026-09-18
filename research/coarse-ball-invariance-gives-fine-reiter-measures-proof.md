---
rg: 2
id: coarse-ball-invariance-gives-fine-reiter-measures-proof
kind: route
title: Take square roots, use log-convexity of the even return moments of the lazy walk, pick the last ratio, and square back
target: coarse-ball-invariance-gives-fine-reiter-measures
requires: []
---

Notation is as in the claim. All vectors below are real and nonnegative, so all inner products are real.

**Step 1 (square roots).** Put `ξ = √ν ∈ ℓ²(G)`, so `‖ξ‖₂ = 1` and `λ_g ξ = √(gν)`. Since `|√a − √b|² ≤ |a − b|`
for `a, b ≥ 0`, we get `‖λ_g ξ − ξ‖₂² ≤ ‖gν − ν‖ ≤ 1` for `g ∈ B_{2K}`. Because `‖λ_gξ − ξ‖₂² = 2 − 2⟨λ_gξ, ξ⟩`,
this gives `⟨λ_g ξ, ξ⟩ ≥ 1/2` for every `g ∈ B_{2K}`.

**Step 2 (return moments).** `P^j = |S'|^{−j} Σ_w λ_w`, where the sum runs over the `|S'|^j` words `w` of length `j`
in `S'`, and each such `w` lies in `B_j`. So for `j ≤ 2K`, `⟨P^j ξ, ξ⟩` is an average of numbers `≥ 1/2`, hence `≥ 1/2`.
`P` is self-adjoint because `S'` is symmetric. Put `c_k = ‖P^k ξ‖₂² = ⟨P^{2k}ξ, ξ⟩`. Then `c_0 = 1` and `c_k ≥ 1/2`
for `0 ≤ k ≤ K`.

**Step 3 (log-convexity).** For `k ≥ 1`, Cauchy–Schwarz gives
`c_k² = ⟨P^{k−1}ξ, P^{k+1}ξ⟩² ≤ c_{k−1} c_{k+1}`. So the ratios `ρ_k = c_k / c_{k−1}` (all positive) are
nondecreasing in `k`. Their product is `ρ_1 ⋯ ρ_K = c_K ≥ 1/2`. The largest ratio `ρ_K` is at least the geometric
mean, so `ρ_K ≥ 2^{−1/K} ≥ 1 − (ln 2)/K`.

**Step 4 (one step of P², then one generator).** Put `η = P^{K−1}ξ ≥ 0`. Then `ρ_K = ⟨P²η, η⟩ / ‖η‖₂²`, and
`⟨P²η, η⟩ = |S'|^{−2} Σ_{s,t∈S'} ⟨λ_{st}η, η⟩`. Put `d_g = ‖η‖₂² − ⟨λ_gη, η⟩`. Each `d_g ≥ 0` by Cauchy–Schwarz, and
`Σ_{s,t} d_{st} = |S'|²(1 − ρ_K)‖η‖₂² ≤ |S'|²(ln 2/K)‖η‖₂²`. Every term is at most the sum. Taking `t = e ∈ S'`
gives, for each `s ∈ S'`,
`‖λ_sη − η‖₂² = 2 d_s ≤ 2|S'|²(ln 2/K)‖η‖₂²`.

**Step 5 (square back).** Let `η̂ = η/‖η‖₂` and `μ = η̂²`, a probability measure with `sμ = (λ_s η̂)²`. Then
`‖sμ − μ‖ = Σ_x |a_x² − b_x²| ≤ ‖a − b‖₂‖a + b‖₂ ≤ 2‖λ_sη̂ − η̂‖₂ ≤ 2|S'|√(2 ln 2/K)`,
with `a = λ_sη̂` and `b = η̂`. For general `g = s_1⋯s_j`, left translation is an ℓ¹ isometry, so
`‖gμ − μ‖ ≤ Σ_i ‖s_iμ − μ‖`.

**Step 6 (support).** `λ_w` moves supports by left multiplication by `w`, so `supp η ⊆ B_{K−1}·supp ν ⊆ B_{r+K−1}`.
The support of `μ` is the support of `η`. ∎
