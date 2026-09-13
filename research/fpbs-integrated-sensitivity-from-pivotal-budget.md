---
rg: 2
id: fpbs-integrated-sensitivity-from-pivotal-budget
kind: route
title: Integrate the pointwise pivotal budget across the critical window
target: fpbs-integrated-sensitivity-universal
requires:
  - fpbs-pivotal-budget-universal
  - fpbs-integrated-pivotal-rate-identity
artifacts:
  - research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md
---

Conditional route recording Proposition 3.1 of the artifact. The budget is
OPEN.

Read PB with the lazy walk. That is the weaker reading: by artifact Section 1,
the simple-walk budget implies the lazy one with the same constant.

1. Integrate the finite Russo identity over `[c,c+epsilon]`:
   `log a_(n,R)(c+epsilon) - log a_(n,R)(c) <= C n log(1+epsilon/c)`.
2. Let `R` tend to infinity, and then `n`. Use `lambda(c)=rho` from the rate
   identity, transferred to the lazy walk by `lambda_L=(1+lambda_S)/2`
   (artifact Lemma 2.2). This gives
   `rho_L <= lambda_L(c+epsilon) <= rho_L (1+epsilon/c)^C`, so
   `lambda_L(c+epsilon) -> rho_L`.
3. The transfer gives `lambda_S(c+epsilon) -> rho_S`.
4. By the rate identity, the IS integral tends to
   `log(lambda_S(c+epsilon)/rho_S)`, which tends to `0`.
