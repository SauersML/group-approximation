---
rg: 2
id: fpbs-lq-two-point-infinite-cluster-reduction-proof
kind: route
title: Bound the q-th power of the truncated two-point function by its first power, sum to the finite susceptibility, factor independent clusters by Tonelli, and count large connections in a ball by Chebyshev
target: fpbs-lq-two-point-infinite-cluster-reduction
requires:
  - fpbs-supercritical-finite-susceptibility
artifacts:
  - research/artifacts/fpbs/docs/lq-infinite-cluster-reduction-2026-09-18.md
---

The complete proof is in Sections 1–3 of the artifact. Apart from the imported
finiteness of `chi^fin(p)` for `p > p_c` (`fpbs-supercritical-finite-susceptibility`,
Hermon–Hutchcroft arXiv:1904.10448v3 Theorem 1.1), it uses only Tonelli,
independence, Hölder, Chebyshev, Fekete and Harris-FKG.

1. **(A).** `0 <= tau^fin <= 1` and `q >= 1` give `(tau^fin)^q <= tau^fin`, and
   `sum_x tau^fin_p(o,x) = chi^fin(p)`. Convexity gives
   `tau^q <= 2^(q-1)((tau^fin)^q + (tau^inf)^q)`.
2. **(B).** Write `|∩_i K^i_inf(o)|` as a sum over `x` of a product of
   indicators, take expectations and factor by independence.
3. **(C).** `#{v : tau_p(o,v) >= e^(-cn)} <= e^(cqn) Z_q(p)`, and
   `|B_n| >= gr^n` by submultiplicativity. So `kappa_p(n) < e^(-cn)` for large
   `n` whenever `e^(cq) < gr`. The ball bound is Hölder with exponents
   `q/(q-1)` and `q`. Uniqueness would give `tau_p >= theta(p)^2 > 0`, which
   is not summable.
