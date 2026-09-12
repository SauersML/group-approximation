---
rg: 2
id: two-root-identities-localize-to-diagonal-blocks
kind: claim
title: For a flag-preserving rank model of EL_3 the two root identities descend to the diagonal and are checked block by block
distinct_from:
  rank-models-of-el3-satisfy-the-two-root-identities: that asserts the identities for every rank model, where extension terms enter the products; this proves that, for a flag-preserving model, the identities on the diagonal blocks in weighted average already force triviality.
  flag-preserving-rank-models-of-el3-reduce-to-their-diagonal: that reduces triviality to the diagonal model; this shows which identities pass to that diagonal model and localizes the gate identity to its blocks.
  el3-unit-root-matrix-units-iff-two-root-identities: that is the algebraic equivalence between the identities and matrix units for one model; this transports the identities through diagonal compression.
artifacts:
  - research/artifacts/el3-rank-model-extensions-2026-09-12.md
---

Let `sigma : EL_3(R) -> M^x` be a homomorphism into a rank ultraproduct, with a flag-preserving
presentation of any lengths (`flag-preserving-rank-models-of-el3-reduce-to-their-diagonal`). Write
`D_i(g_i) = (+)_t rho_(i,t)(g)`, `N_ab = sigma(x_ab(1)) - 1` and
`N^(i,t)_ab = rho_(i,t)(x_ab(1)) - 1`.

1. **Descent and additivity.** For every noncommutative polynomial `P` in the six displacements,
   `rk(P(N^D)) <= rk(P(N))`, and `rk(P(N^D))` is the ω-limit of `sum_t rk(P(N^(i,t))) / n_i`. So
   any identity among the root displacements passes from `sigma` to its diagonal model. It holds
   there exactly when it holds on the blocks in dimension-weighted average.
2. **Localized gate.** Let `R` be a unital algebra of characteristic `p` with no unital ring
   homomorphism into any characteristic-`p` rank ultraproduct, for instance a simple ring that is
   not directly finite, and let `char k = p`. If
   `sum_t rk((N^(i,t)_12)^2) + rk(N^(i,t)_23 N^(i,t)_12) = o(n_i)`, then `sigma` is trivial. In
   characteristic two only the second term is needed.

So for flag-preserving models the gate identity `N_23 N_12 = 0` is a statement about the diagonal
blocks alone. The off-diagonal extension terms are invisible to it.

**ESTABLISHED** by `two-root-identities-localize-proof` (artifact Section 4.4, Proposition 9).
