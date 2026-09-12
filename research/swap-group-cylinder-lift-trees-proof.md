---
rg: 2
id: swap-group-cylinder-lift-trees-proof
kind: route
title: Block decomposition of the binary swap-group algebra, transported to every cylinder by the corner embeddings
target: swap-group-cylinder-lift-trees-halve-but-never-refine
requires: [binary-leavitt-unit-group-is-simple]
artifacts:
  - research/artifacts/defect-piece-covariance-letterwise-firewall-2026-09-12.md
---

Artifact Section 3, Lemma 3.1 and Theorem 3.2.

1. **Blocks.** `F_2[S_3] = F_2[S_3]e x F_2[S_3](1 + e)`. On the first block `c` is trivial and `p_0, p_1 -> 0`.
   The second is `M_2(F_2)` through `u = [[1,1],[0,1]]`, `v = [[1,0],[1,1]]`, where `p_0 = diag(1,0)`,
   `p_1 = diag(0,1)`. So `p_0, p_1` are orthogonal idempotents with sum `1 + e`, and the swap conjugates
   `p_0` to `p_1`.
2. **Transport.** `iota_w` extends linearly to a ring homomorphism, and `g iota_w(h) g^-1 = iota_(gw)(h)` for
   prefix replacements `g`. This gives the orthogonal split and covariance.
3. **Ranks.** Prefix replacements make `rk(E_w)` constant, and the swap at `w` gives equal halves. Simplicity
   makes a nontrivial model injective, so `sigma(c_w) != 1` and `E_w != 0`. Faithfulness gives `eps > 0`.
4. **Evaluation.** `ev(iota_w(p_i)) = 1_[wi]` (four terms, the complement cancels) and
   `ev(iota_(wi)(1 + e)) = 1_[wi]` (two terms, `c + c^2 = 1`). Rank subadditivity gives
   `rk(A_(wi) - E_(wi)) >= eps/2`.
