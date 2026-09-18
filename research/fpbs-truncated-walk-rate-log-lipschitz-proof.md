---
rg: 2
id: fpbs-truncated-walk-rate-log-lipschitz-proof
kind: route
title: Bound open pivotals of a truncated event by the certificate length and integrate Russo from pc
target: fpbs-truncated-walk-rate-log-lipschitz
requires:
  - fpbs-critical-walk-correlation
artifacts:
  - research/artifacts/fpbs/docs/truncated-russo-lipschitz-2026-09-17.md
---

Complete written proof in Sections 1, 2 and 4 of the artifact. No computation is used.

1. **Truncated Russo–Lipschitz inequality (Lemma 1.1).**
   * `A_(x,M)={d_omega(e,x)<=M}` is increasing and depends on the finite ball `B_M`.
   * Every open pivotal edge lies on one fixed open path of length at most `M`.
   * So Russo gives `d/dp log P_p(A) <= M/p`, hence `P_p(A) <= (p/q)^M P_q(A)`.
2. **Rates.**
   * Harris–FKG and the triangle inequality for `d_omega` make `a^(L)_n` supermultiplicative.
   * It is at least `p^n`, so Fekete gives `lambda_L = lim = sup`.
   * Averaging Lemma 1.1 over `X_n` gives the log-Lipschitz bound.
   * Schramm's lemma `a_n(p_c)<=rho^n` (`fpbs-critical-walk-correlation`) gives `rho (p/p_c)^L`.
   * Monotone convergence in `L` at fixed `n`, plus exchanging two suprema, gives `sup_L lambda_L = lambda`.
3. **Corollary.** Uniqueness and FKG give `tau_t >= theta(t)^2`. Divide by it.
