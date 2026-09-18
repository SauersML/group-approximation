---
rg: 2
id: fpbs-relative-stage-costs-bound-cost-by-stage-liminf-proof
kind: route
title: Sum near-optimal relative graphings along a fast-converging subsequence of stages
target: fpbs-relative-stage-costs-bound-cost-by-stage-liminf
requires: []
artifacts:
  - research/artifacts/fpbs-relative-fixed-price-decomposition-2026-09-17.md
---

The complete proof is §1 of the artifact and is self-contained. Its only input
is the definition of `relC(R;S)` as the infimum of `c(Φ)` over graphings
`Φ ⊆ R` with `S ∨ Φ = R`.

1. Let `c = liminf c_n < ∞` and `ε > 0`. Choose `n_k` with
   `|c_{n_k} − c| < ε 2^{-k}`. Then `(c_{n_{k+1}} − c_{n_k})^+ < ε 2^{1-k}`.
2. Choose a graphing `Ψ` of `R_{n_1}` of cost `< c + 2ε`, and graphings `Φ_k`
   with `R_{n_k} ∨ Φ_k = R_{n_{k+1}}` of cost `< 3ε 2^{-k}`.
3. By induction, `Ψ ∪ Φ_1 ∪ ⋯ ∪ Φ_{k-1}` generates `R_{n_k}`. These relations
   increase to `E_a`, so `Ψ ∪ ⋃Φ_k` generates `E_a`.
4. Its cost is `< c + 5ε`. ∎

In the integer case, choose `c_{n_k} = c` and relative graphings of cost
`< ε 2^{-k}`.
