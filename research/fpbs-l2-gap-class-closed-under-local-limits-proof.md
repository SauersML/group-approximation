---
rg: 2
id: fpbs-l2-gap-class-closed-under-local-limits-proof
kind: route
title: Transport finite-ball test forms, use the Duminil-Copin–Tassion finite-set criterion, and bound norms by local row sums
target: fpbs-l2-gap-class-closed-under-local-limits
requires: []
artifacts:
  - research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md
---

A complete written proof is in the artifact. The only import is quoted
verbatim there, in Section 1.

**Import.** [DT] Duminil-Copin–Tassion, arXiv:1502.03050v3, from the TeX
source `sharpnessPercoIsing-H.tex`, fetched 2026-09-17.

* Lines 314–322 define
  `tilde beta_c = sup{beta : varphi_beta(S) < 1 for some finite S containing 0}`
  and state "This directly implies that $\tilde{\beta_c}=\beta_c$".
* Lines 349–354 give the nearest-neighbour form `p = 1 - e^{-beta}`, with
  `varphi_p(S) = p sum_{x in S} sum_{y notin S, {x,y} in E} P_p[0 <->_S x]`.
* Lines 398–412 give the remark that `tilde beta_c` is lower semicontinuous
  under agreement of balls, and hence so is `beta_c`.

**Steps.**

1. **Theorem 2.1.**
   * For nonnegative `f` and `g` supported in `B_r` and `R >= r`, the form
     `<f, T_{p,R} g>` built from connections inside `B_R` is a function of the
     rooted ball.
   * Transport it to `G_k` for `k >= k(R)`. It is bounded there by
     `||T^{G_k}_p|| ||f|| ||g||`.
   * Take the `liminf` in `k`, then monotone convergence in `R`.
2. **Lemma 1.1.**
   * If `p < p_c(G)`, there is a finite `S` with `varphi_p(S) < 1`, by the
     supremum definition and monotonicity in `p`.
   * `varphi_p(S)` is ball-local, so `p <= p_c(G_k)` for large `k`.
3. **Theorem 3.1.**
   * Part (a) follows from Theorem 2.1 and monotonicity of the norm in `p`.
   * Part (b) uses
     `limsup Gamma_M - liminf p_c >= limsup (Gamma_M - p_c)`.
   * The level sets `{g_M >= delta}` equal `U_(M,delta)`. This uses left
     continuity of `tau_p`, as a supremum of increasing polynomials.
4. **Corollary 3.2.**
   * The norm bound passes to the limit.
   * Harris–FKG gives `tau_p >= theta^2` at uniqueness. So a bounded operator
     on `[0, p_c+delta]` rules out uniqueness there.
   * The pivotal bound is Theorem 4.1 of
     `research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`.
5. **Proposition 4.1.**
   * On finite transitive graphs the norm equals the row sum.
   * On amenable transitive graphs, Følner sets give `||T_p|| >= chi_r(p)`.
   * `chi_r` is ball-local, and `chi_r(p) -> infinity` for `p > p_c(G)`
     because `theta(p) > 0`.
   * So `Gamma_M(G_k) <= p` eventually, for every `p > p_c(G)`.
