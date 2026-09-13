---
rg: 2
id: fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels-proof
kind: route
title: Integrate the bounded pivotal count through finite Russo identities
target: fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels
requires:
  - fpbs-l2-gap-gives-bounded-pivotal-counts
artifacts:
  - research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md
---

Written proof of Corollary 4.2 in the artifact.

* **The norm is finite up to `p0`.** `tau_p` is pointwise nondecreasing in
  `p`, and the operator norm of a nonnegative kernel is monotone in the
  kernel. So for `p <= p0 < p1 < p_(2->2)` we have
  `||T_p|| <= ||T_(p1)|| < infinity`. The prerequisite then gives
  `E_p[N_(n,R)|E_(n,R)] <= C_0` for `p` in `(0,p0]`.
* **PB and RATE** follow at once: `C_0 <= C_0 n`, and
  `n^(-1) log(1+C_0/n) -> 0 < lambda_0/2`.
* **IS and NC.** `B_R` is finite, so Russo's formula gives
  `d/dp log a_(n,R)(p) = E_p[N_(n,R)|E_(n,R)]/p`. With `c=p_c>0` and
  `epsilon <= p0-c`, for every `R>=n`,

      0 <= n^(-1) log( a_(n,R)(c+epsilon) / a_(n,R)(c) ) <= C_0 n^(-1) log(1+epsilon/c).

  As `R -> infinity` both probabilities increase to positive limits. So the
  inner limit exists and satisfies the same bounds, and the limit in `n` is
  `0`. For the simple walk this shows the IS integral is `0` for every small
  `epsilon`. For the lazy walk it shows `B(epsilon) = 0 < -log rho_L`.
