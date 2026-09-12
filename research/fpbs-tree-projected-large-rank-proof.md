---
rg: 2
id: fpbs-tree-projected-large-rank-proof
kind: route
title: Tree lift bounds p_c, Schur blocks and Kesten bound the adjacency norm
target: fpbs-tree-projected-large-rank-strict-thresholds
requires: []
---

Notation as in the target. Write `Gamma_q = pi^(-1)(q)` and `m_t = #{g in S : pi(g) = t}`.

1. **`p_c <= 1/(2n-1)`.**
   * `S` generates `Gamma`, so `pi(S)` generates `F_n`, and every basis letter
     lies in `pi(S)`.
   * For each letter `t` choose `g_t in S` with `pi(g_t) = t` and
     `g_(t^(-1)) = g_t^(-1)`. Send a reduced word `t_1 ... t_R` to
     `g_(t_1) ... g_(t_R)`.
   * Distinct reduced words have distinct projections, so the map is injective,
     and consecutive prefixes are adjacent in `Cay(Gamma,S)`.
   * So `Cay(Gamma,S)` contains a copy of the `2n`-regular tree, and
     `p_c(Cay(Gamma,S)) <= p_c(T_(2n)) = 1/(2n-1)`.
2. **`||A|| <= v + 2 m sqrt(2n-1)`.**
   * Let `f, g` be finitely supported on `Gamma`, and put
     `F(q) = ||f|_(Gamma_q)||_2`, `G(q) = ||g|_(Gamma_q)||_2`.
   * Every edge joins `Gamma_q` to `Gamma_(qt)` with `t in {1} ∪ B ∪ B^(-1)`.
     The block of `A` between these fibres has row sums `c_t` and column sums
     `c_t`, where `c_1 = v` and `c_t = m_t`; symmetry of `S` gives
     `m_(t^(-1)) = m_t`.
   * By Schur's test each block has norm at most `c_t`. Hence
     `|<f, A g>| <= sum_q sum_t c_t F(q) G(qt) = <F, K G>`, with
     `K = v I + sum_t m_t rho(t)` on `l2(F_n)`.
   * Entrywise `0 <= K <= v I + m A_(T_(2n))`. For nonnegative kernels the
     operator norm is monotone, so `||A|| <= ||K|| <= v + m ||A_(T_(2n))||`.
   * Kesten: `||A_(T_(2n))|| = 2 sqrt(2n-1)`.
3. **`p_{2->2} >= 1/||A||`.**
   * `tau_p(x,y)` is at most the sum of `p^(length)` over paths from `x` to `y`,
     so entrywise `T_p <= sum_(l >= 0) p^l A^l`.
   * If `p ||A|| < 1` then `||T_p|| <= sum_l (p ||A||)^l < infinity`.
4. **`p_{2->2} <= p_u`.** For `p > p_u` the infinite cluster is unique, so
   `tau_p(x,y) >= theta(p)^2 > 0` for all `x, y`, and `T_p` is unbounded on the
   infinite graph. This is Hutchcroft arXiv:1804.10191, Section 2.
5. **Conclusion.** The hypothesis gives `1/(2n-1) < 1/(v + 2 m sqrt(2n-1)) <= 1/||A||`.
   Steps 1, 3 and 4 give `p_c <= 1/(2n-1) < 1/||A|| <= p_{2->2} <= p_u`.

**Table check.** Put `x = sqrt(2n-1)`.
* With `m = 1, v = 2`, the condition is `x^2 - 2x - 2 > 0`, i.e. `x > 1 + sqrt 3`.
  That holds from `n = 5`, where `x = 3`, and fails at `n = 4`.
* With `m = 2, v = 2`, it is `x > 2 + sqrt 6`, which holds from `n = 11` and
  fails at `n = 10`.
