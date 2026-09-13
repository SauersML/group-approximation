---
rg: 2
id: product-of-tree-groups-factorwise-howe-moore-proof
kind: route
title: Run Ciobotaru's contraction-group criterion on one escaping coordinate of the product polar decomposition
target: product-of-tree-groups-has-factorwise-howe-moore
requires: []
artifacts:
  - research/artifacts/product-tree-mixing-transfer-2026-09-12.md
---

# Proof

Artifact Section 0 transcribes the lemmas used, with page numbers, from C. Ciobotaru,
*A unified proof of the Howe--Moore property*, arXiv:1403.0223v2. Section 1 is the
full argument. Separability of `ℋ` may be assumed (Lemma 2.4 there).

1. **Polar decomposition.** Lemma 4.7 and Example 4.10 give `G_i = K_i A_i^+ K_i'`,
   `K_i, K_i'` compact, `A_i^+ = {a_i^m : m >= 0}` with `a_i` hyperbolic. So
   `G_1 × G_2 = (K_1 × K_2)(A_1^+ × A_2^+)(K_1' × K_2')` with an abelian middle
   semigroup. By Lemma 2.9 it suffices to show `⟨π(g_n)v, w⟩ → 0` for sequences
   `g_n = (a_1^(m_n), a_2^(l_n)) → ∞`.
2. **Escape.** After passing to a subsequence, `m_n → ∞` or `l_n → ∞`; say `m_n → ∞`.
   For `u ∈ U_(a_1)^+` we get `g_n^(-1)(u, e)g_n = (a_1^(-m_n) u a_1^(m_n), e) → e`, so
   `U_α^+ ⊇ U_(a_1)^+ × {e}`, and likewise for `U^-`.
3. **Generation.** By Corollary 4.18, `closure⟨U_(a_1)^+, U_(a_1)^-⟩` is normal in `G_1`,
   and it is nontrivial, as in the proof of Theorem 4.19. Topological simplicity makes
   it `G_1`. So `closure⟨N_α^+, N_α^-⟩ ⊇ G_1 × {e}`.
4. **Normal weak limit.** Suppose `|⟨π(g_n)v, w⟩| >= C > 0` along a subsequence. The
   `π(g_n)` commute pairwise, so a further subsequence converges weakly to a normal
   `E ≠ 0` (Lemma 2.13). The computation in the proof of Lemma 3.1 gives
   `π(u_+) E π(u_-) = E` for `u_± ∈ U_α^±`. Then `closure E(ℋ)` is `U_α^+`-invariant,
   `closure E^*(ℋ)` is `U_α^-`-invariant, and `E^*E = EE^* ≠ 0` gives a nonzero `ψ` in
   their intersection. It is invariant under `⟨N_α^+, N_α^-⟩ ⊇ G_1 × {e}`, contradicting
   the hypothesis on `π`.

**Corollary.** If the action is ergodic for each `G_i`, then `L^2_0` has no nonzero
`G_i`-invariant vector, so `μ(gA ∩ B) → μ(A)μ(B)` as `g → ∞`. A sequence tending to
infinity in a discrete subgroup tends to infinity in `G_1 × G_2`.
