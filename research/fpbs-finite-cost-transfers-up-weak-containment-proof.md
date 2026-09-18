---
rg: 2
id: fpbs-finite-cost-transfers-up-weak-containment-proof
kind: route
title: Transfer each stage's summable graphing tail with its own conjugator, relative to the subgroup relation already built
target: fpbs-finite-cost-transfers-up-weak-containment
requires:
  - burton-kechris-cost-usc-and-maximum-action
  - abert-weiss-free-actions-weakly-contain-bernoulli
artifacts:
  - research/artifacts/fpbs-finite-cost-transfers-up-weak-containment-2026-09-18.md
---

Theorem A is proved in artifact §2 and §3. It uses only item 1 of
`burton-kechris-cost-usc-and-maximum-action`, Burton–Kechris Theorem 2.3
(Kechris Prop 10.1): "Let a ∈ A(Γ, X, µ), b ∈ A(Γ, Y, ν) with (X, µ), (Y, ν)
non-atomic. Then a ≼ b ⇐⇒ a ∈ {c ∈ A(Γ, X, µ) : c ≅ b}‾".

1. **Lemma 1 (pattern transfer).** Weak convergence of conjugates
   `S b S^{-1} → a` carries any finitely many Boolean combinations of sets
   `(g^a)^{-1} A_i` to `b`, with error `< η`. It keeps `ν(S^{-1} A_i) = μ(A_i)`
   exactly.
2. **Lemma 2 (finitely many words).** Suppose `a` is free and
   `E_{a|K} ∨ Φ ⊇ E_{a|⟨K,s⟩}`. Then the words of value `s` have domains
   covering `X`, and finitely many of them cover measure `1 − δ`.
3. **Tails.** Take `E_{a|H} ∨ Φ = E_a` with `cost(Φ) < c + ε`. For
   `H_n = ⟨H, γ'_1..γ'_n⟩`, the tail mass `t_n` of the pieces with labels
   outside `H_n` tends to 0. Also `E_{a|H_n} ∨ (tail) = E_a`.
4. **Stage `k`.** Transfer the tail words that reach
   `S_k = {γ'_{n_k+1}, …, γ'_{n_{k+1}}}`, and add fix-ups `(Y ∖ U_s, s)`. This
   gives `E_{b|H_{n_k}} ∨ Ψ_k ⊇ E_{b|H_{n_{k+1}}}` with
   `cost(Ψ_k) ≤ t_{n_k} + ε 2^{-k}`.
5. **Induction and sum.** Induction on `k` gives
   `E_{b|H} ∨ ⋃ Ψ_k = E_b`, with total cost `≤ c + 4ε`.

The Bernoulli consequences (artifact §4, Corollary 1) add Abért–Weiss
Theorem 1, `abert-weiss-free-actions-weakly-contain-bernoulli`: every free
action weakly contains every Bernoulli action.
