---
rg: 2
id: fpbs-mal-graphing-b-length-weighted-floor-proof
kind: route
title: Unfold each chord along a shortest double-coset word into b-seeds, then apply fold exactness and the Bernoulli seed-density floor
target: fpbs-mal-graphing-b-length-weighted-floor
requires:
  - fpbs-mal-fold-closure-exactness
  - fpbs-weakly-bernoulli-fold-seeds-have-density-floor
artifacts:
  - research/artifacts/fpbs-chord-unfolding-length-floor-2026-09-18.md
  - experiments/fpbs-chord-unfolding-2026-09-17/coset_b_length.py
  - experiments/fpbs-chord-unfolding-2026-09-17/coset_b_length_out.txt
---

The complete proof is §2 of the artifact (Theorem B).

1. **Unfold.** Take a piece `h|_D` with `r = |h|_{K,b}`, written
   `h = k_r b^{ε_r} ⋯ k_1 b^{ε_1} k_0`. For `x ∈ D`, the path from `x` to
   `h x` alternates `R_K`-moves with `b`-steps. The `i`-th step lies in the
   graph of `b|_{g_i D}`, where `g_i = q_i` or `b^{-1} q_i` and
   `q_i = k_{i-1} b^{ε_{i-1}} ⋯ k_0`. So
   `(x, h x) ∈ R_K ∨ b|_{A(h, D)}`, where `A(h, D) = ⋃_i g_i D` has
   `μ(A(h, D)) ≤ r μ(D)`.
2. **Union.** `A = ⋃_j A(h_j, D_j)` has
   `μ(A) ≤ Σ_j |h_j|_{K,b} μ(D_j)`, and
   `R_L = R_K ∨ Φ ⊆ R_K ∨ b|_A ⊆ R_L`.
3. **Exactness.** By `fpbs-mal-fold-closure-exactness` (freeness is used
   here), `R_K ∨ b|_A = R_L` forces `cl(A)` to be conull. Hence
   `μ(A) ≥ σ_b(X)`.
4. **Floor.** By `fpbs-weakly-bernoulli-fold-seeds-have-density-floor`,
   `σ_b(X) ≥ 1/80` on actions weakly contained in Bernoulli.

The corollaries in §3 are immediate: bound the weight by `r · mass`, or
split the labels at the length `T = 1/(160 ε)`. For `Gamma_mal`, the pair
`H_n ≤ H_{n+1}` is `K ≤ L` with `b = b_{n+1}`, and restrictions of Bernoulli
shifts to `H_{n+1}` are Bernoulli, as used in the w8 claim.
