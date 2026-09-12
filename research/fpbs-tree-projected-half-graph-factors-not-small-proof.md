---
rg: 2
id: fpbs-tree-projected-half-graph-factors-not-small-proof
kind: route
title: Sum the last-crossing fibre bound over the quotient against the divergence of the susceptibility
target: fpbs-tree-projected-half-graph-factors-not-small
requires:
  - fpbs-tree-projected-branch-share-last-crossing-bound
  - fpbs-fibre-summed-connectivity-operator
---

Notation as in the target.

1. **`sup_(p < p_c) chi_p = infinity`.**
   * Duminil-Copin–Tassion (arXiv:1502.03050, Theorem 1.2) apply because
     `Cay(Gamma,S)` is transitive: `p_c = sup{p : φ_p(Σ) < 1 for some finite Σ ∋ o}`,
     where `φ_p(Σ) = p sum_((x,y) in ∂_E Σ) P_p(o <-> x inside Σ)`.
   * If `chi_p < infinity`, then `φ_p(B_k) <= p d sum_(x in ∂B_k) tau_p(o,x) -> 0`
     as `k -> infinity`. So `φ_p(B_k) < 1` for some `k`.
   * `φ_(p')(B_k)` is a polynomial in `p'`, so it stays below 1 for `p'` near
     `p`. Hence `p < p_c`, and `chi_(p_c) = infinity`.
   * Each `tau_p(o,x)` is a nondecreasing left-continuous supremum of
     finite-volume polynomials, so `chi_p` is left-continuous. Therefore
     `sup_(p < p_c) chi_p = chi_(p_c) = infinity`.
2. **Summing the fibre bound.**
   * For `p < p_c` and every reduced word `w = s_1 ... s_D`, item 4 of
     `fpbs-tree-projected-branch-share-last-crossing-bound` gives
     `sigma_p(w) <= chi^H_p prod_(j<=D) lambda_p(s_j)`. For the empty word,
     `sigma_p(1) = chi^H_p`.
   * Reduced words of length `R >= 1` are the letter sequences with
     `s_(j+1) != s_j^(-1)`, so
     `sum_(|w| = R) prod_j lambda_p(s_j) = u_p^T M_p^(R-1) 1`, where
     `u_p(s) = lambda_p(s)`.
   * Summing over `w`:

     ```text
     chi_p = sum_w sigma_p(w) <= chi^H_p ( 1 + sum_(R >= 1) u_p^T M_p^(R-1) 1 ).
     ```

3. **Contradiction.**
   * Suppose `chi^H_(p_c) < infinity` and `rho(M_(p_c)) < 1`.
   * Every half graph is a subgraph, so `chi^(s)_(p_c) <= chi^H_(p_c) < infinity`,
     and all entries of `M_(p_c)` and `u_(p_c)` are finite.
   * All quantities are nondecreasing in `p`. So for every `p < p_c`,
     `chi_p <= chi^H_(p_c) (1 + sum_R u_(p_c)^T M_(p_c)^(R-1) 1)`.
   * `M_(p_c)` is a fixed nonnegative `2n × 2n` matrix of spectral radius
     below 1, so the series converges. Then `sup_(p < p_c) chi_p < infinity`,
     contradicting step 1.
4. **Consequences.**
   * *Amenable `H` with `p_c < p_{2->2}`.* `||T_(p_c)|| < infinity` by
     definition of `p_{2->2}`. The equality case of
     `fpbs-fibre-summed-connectivity-operator` gives
     `chi^H_(p_c) = <delta_1, S_(p_c) delta_1> <= ||S_(p_c)|| = ||T_(p_c)||`. So
     step 3 forces `rho(M_(p_c)) >= 1`.
   * *Uniform factors.* Each row of `M` has `2n-1` entries equal to `lambda`,
     giving Perron roots `(2n-1) lambda` for `M` and `(2n-1) lambda^2` for `N`.
