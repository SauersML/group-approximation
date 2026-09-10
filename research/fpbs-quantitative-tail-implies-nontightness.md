---
rg: 2
id: fpbs-quantitative-tail-implies-nontightness
kind: route
title: Positive averaged route tails at every fixed radius preclude uniform tightness
target: fpbs-cost-one-routes-cannot-be-uniformly-tight
requires:
  - fpbs-quantitative-routing-tail-bound
artifacts:
  - research/artifacts/fpbs/routing-obstruction-continuation.md
---

Apply inequality (1) with delta_n tending to zero for each fixed R. The limiting lower bound h/d is positive and independent of R. Uniform tightness for every generator would force the finite average of these tails to tend uniformly to zero as R increases, contradicting this bound.
