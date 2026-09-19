---
rg: 2
id: fpbs-connectivity-decay-gives-heavy-walk-green-visits
kind: claim
title: Uniform connectivity decay at a parameter gives a heavy-tailed symmetric walk with finitely many expected visits to the cluster of the origin
distinct_from:
  fpbs-green-visit-criterion-universal: that fixes simple random walk and asks for finite expected visits above p_c; this lets the step law depend on p and shows that uniform decay of tau_p already produces such a law, so the walk-visit family reaches the decay threshold.
  fpbs-worst-pair-connectivity-rate-positive-above-pc-universal: that asks for one exponentially poorly connected point in each large ball; this assumes decay of tau_p at every far point, at any rate, and converts it into a walk-visit certificate.
artifacts:
  - research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md
---

**ESTABLISHED.** Theorem 4 of
`research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md`.

Let `Gamma` be infinite and finitely generated, and `f : Gamma -> [0,1]` with
`sup_{|y|>r} f(y) -> 0`. Then some symmetric probability measure `mu` (a
mixture `sum_k (1/k - 1/(k+1)) Unif(B_{R_k})` with fast-growing radii) has
`sum_n E f(X_n) < infinity`. In particular:

* if `tau_p(e,y) -> 0` as `|y| -> infinity`, then some symmetric `mu` has
  `A_mu(p) = sum_n P_p(e <-> X_n) < infinity`;
* with `p_dec = sup{p : tau_p(e,.) -> 0 at infinity}`,

  ```text
  p_dec <= sup_mu p_A^mu <= sup_mu p_vis^mu <= p_u.
  ```

  The last inequality is `fpbs-stationary-set-recurrence-separates`.

No nonamenability or percolation input is used. The bound is Young's
inequality `||nu_{k_1} * ... * nu_{k_n}||_inf <= 1/|B_{R_max}|` together with
the tail `P(max index < m) = (1-1/m)^n`.

**Scope.** This is an ordering result. Uniform decay at `p > p_c` already
excludes uniqueness at `p` directly through `tau >= theta^2`. The theorem shows
that the walk-visit family, once the step law is free, is at least as strong
as uniform decay, and so it places `fpbs-stationary-set-relative-gap-universal`
below uniform decay past `p_c`.
