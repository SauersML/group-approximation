---
rg: 2
id: fpbs-subscale-chemical-saturation-equivalence-proof
kind: route
title: Push sub-scale truncated rates through the log-Lipschitz bound and exchange suprema at pc
target: fpbs-integrated-sensitivity-iff-subscale-chemical-saturation
requires:
  - fpbs-truncated-walk-rate-log-lipschitz
  - fpbs-integrated-pivotal-rate-identity
artifacts:
  - research/artifacts/fpbs/docs/truncated-russo-lipschitz-2026-09-17.md
---

Complete written proof in Section 3 of the artifact. No computation is used.

* **(SE) implies (IS).**
  * `lambda_(L(epsilon))(p_c+epsilon) <= rho exp(epsilon L(epsilon)/p_c) -> rho`
    by `fpbs-truncated-walk-rate-log-lipschitz`.
  * Dividing by the ratio, which tends to 1, gives `limsup lambda(p_c+epsilon) <= rho`.
  * Monotonicity and `lambda(p_c)=rho` (`fpbs-integrated-pivotal-rate-identity`) give equality.
* **(IS) implies (SE).**
  * Take `L(epsilon)=epsilon^(-1/2)`.
  * Monotonicity in `p` and `sup_L lambda_L(p_c)=lambda(p_c)=rho` give
    `liminf lambda_(L(epsilon))(p_c+epsilon) >= rho`.
  * (IS) gives `lambda(p_c+epsilon) -> rho`, so the ratio tends to 1.
* **Quantitative form.** Apply the bound `rho exp(epsilon L/p_c)` with `L < p_c Delta/epsilon`.
