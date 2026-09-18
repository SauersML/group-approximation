---
rg: 2
id: fpbs-truncated-walk-rate-log-lipschitz
kind: claim
title: Chemically truncated walk connection rates are log-Lipschitz with slope constant and below rho times (p/pc)^L
artifacts:
  - research/artifacts/fpbs/docs/truncated-russo-lipschitz-2026-09-17.md
distinct_from:
  fpbs-integrated-pivotal-rate-identity: that identifies the integrated untruncated pivotal sensitivity with log(lambda(p)/rho); this bounds the rates of the chemically truncated events d_omega(e,X_n)<=Ln, whose pivotal count is at most Ln, and shows lambda is the increasing supremum of these continuous rates.
  fpbs-l2-gap-gives-bounded-pivotal-counts: that bounds untruncated pivotal counts by a full-space bubble under an l2 gap; this uses no gap and bounds only the truncated counts by path length.
---

Let `G` be a nonamenable Cayley graph with simple random walk spectral radius `rho`.
For `L>=1`, let `lambda_L(p)=lim_n P_p(d_omega(e,X_n)<=Ln)^(1/n)`. Then:

* the limit exists and is a supremum (Harris supermultiplicativity);
* `lambda_L(q) <= lambda_L(p) <= (p/q)^L lambda_L(q)` for `q<=p`, so `lambda_L` is continuous;
* `lambda_L(p) <= rho (p/p_c)^L` for `p>=p_c`;
* `sup_L lambda_L(p) = lambda(p)`.

Corollary (forced chemical stretch): at any `t` with `theta(t)>0` and a unique
infinite cluster,
`P_t(d_omega(e,X_n)<=Ln | e<->X_n) <= theta(t)^(-2) rho^n (t/p_c)^(Ln)`.
This decays exponentially for `L < log(1/rho)/log(t/p_c)`.

Theorem 1 and Corollary 3 of the artifact.
