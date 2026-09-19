---
rg: 2
id: steurer-parallel-repeated-unique-games-rounding-citation
kind: route
title: Import Theorems 1, 3, 4 and 7 of Steurer, Improved Rounding for Parallel Repeated Unique Games (APPROX-RANDOM 2010)
target: steurer-parallel-repeated-unique-games-rounding
requires: []
---

This is a literature import, and credit is the author's in full. The quotations
come from text that `pypdf` extracted on 2026-09-19 from
`dsteurer.org/paper/roundpar2.pdf`. Line breaks and hyphenation have been
undone, and symbols have been transcribed.

## Quotations

* **Abstract.** "Let G be a unique game with alphabet size k. Suppose the
  semidefinite value of G, denoted sdp(G), is at least 1−ε. Then, we show that
  the optimal value opt(G^ℓ) of the ℓ-fold repetition of G is at least
  1 − O(√(ℓ ε log k)). This bound confirms a conjecture of Barak et al. (2008),
  who showed a lower bound that was worse by √(ℓ ε log(1/ε))."
* **Repetition (Section 1).** "ℓ-fold parallel repetition takes a unique game G
  with vertex V and alphabet Σ and outputs a unique game, denoted G^ℓ, with
  vertex set V^ℓ and alphabet Σ^ℓ. For every ℓ-tuple (u1,v1,π1),...,(uℓ,vℓ,πℓ)
  of constraints in G, the game G^ℓ contains a constraint (u,v,π), where
  u = (u1,...,uℓ), v = (v1,...,vℓ), and π is the permutation of Σ^ℓ obtained by
  applying πi to the ith coordinate."
* **Theorem 1.** "For every unique game G with alphabet size k and
  sdp(G) ≥ 1−ε, opt(G^ℓ) ≥ 1 − O(√(ℓ ε log k))."
* **Proof of Theorem 1.** "Theorem 3 shows that sdp+(G) ≥ 1 − O(ε log k). The
  intermediate relaxation satisfies sdp+(G^ℓ) ≥ sdp+(G)^ℓ (Lemma 9). Hence,
  sdp+(G^ℓ) ≥ 1 − O(ℓ ε log k). On the other hand, Theorem 8 implies that
  opt(G^ℓ) ≥ 1 − O(√η) if sdp+(G^ℓ) ≥ 1 − η."
* **Theorem 4.** "Let H = G^ℓ be a parallel repetition of a unique game G with
  alphabet size k. Suppose sdp(H) ≥ 1−ε. Then, opt(H) ≥ 1 − O(√(ε log k)).
  ... [3] show the same bound with k being replaced by the alphabet size of H.
  In our setting, H has alphabet size k^ℓ. ... For more repetitions, our bound
  is strictly stronger. In this sense, parallel repeated unique games are easier
  to approximate than general unique games." The paper notes "(We omit the
  proof.)"
* **SDP (Section 2.2, (2.3)–(2.5)).** "sdp(G) := max E_{(u,v,π)∼G}
  Σ_{i∈Σ} ⟨u_i, v_π(i)⟩, where we maximize over all collections {u_i} of vectors
  that satisfy Σ_{i∈Σ} ‖u_i‖² = 1 (u ∈ V), ⟨u_i, u_j⟩ = 0 (u ∈ V, i ≠ j ∈ Σ)."
* **Theorem 7 ([6] = Feige–Lovász).** "For every unique game G and number
  ℓ ∈ ℕ, we have sdp(G^ℓ) = sdp(G)^ℓ." Appendix A.1: "Feige and Lovász [6]
  show the upper bound on opt(G). (In particular, they show opt(G^ℓ) ≤ sdp(G^ℓ)
  and sdp(G^ℓ) = sdp(G)^ℓ.)"

## Reading

1. **Logarithm and constant.** The logarithm is read as the natural one. The
   `O(·)` of Theorem 1 is read as one absolute constant `C_1`, and `C_1 >= 1`
   may be assumed. The statement is independent of `ℓ`, `ε` and `k`, because
   the proof composes three statements that each have absolute constants:
   Theorem 3, Lemma 9 (exact) and Theorem 8.
2. **Vacuous range.** When `C_1 sqrt(ℓ ε ln k) >= 1`, the bound says nothing,
   and it remains true.
3. **The SDP is the graph's basic SDP.** Constraints (2.4)–(2.5) and objective
   (2.3) are exactly the program in `spectral-gap-no-output-kill-proof`, item 2.
   That program has constraint matrix units, the block constraint
   `sum_a X_(ua,ua) = 1` and off-diagonal zeros within each block. So the
   graph's polynomial-time solver applies to the same `sdp(G)`.
4. **Dependence of (S2).** (S2) is used only by the "general-completeness"
   clause of `parallel-repetition-cannot-substitute-rounds-for-alphabet`. That
   downstream claim's main clause, with product completeness, uses (S1) alone.
   Feige–Lovász state their multiplicativity for two-prover (bipartite) games,
   and the downstream claim is stated only for bipartite games, which are the
   games of `sqrt-scale-unique-games-hardness`.
