---
rg: 2
id: fpbs-traffic-variational-cost-identities
kind: claim
title: Finite routing plans give exact variational formulas for both action costs
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/responses/51_0909-211602.md
---

With the notation of the descent bound, over all finite routing plans on the source action Y,

C(Y) = inf B,    C(X) = inf (B + J_pi),    so   C(X) - C(Y) = inf [ (B - C(Y)) + J_pi ],

with both bracketed terms nonnegative. Hence C(X) = C(Y) exactly when there are plans with B tending to C(Y) and J_pi tending to 0 simultaneously. The simultaneity is the whole content: plans with zero defect always exist by lifting target plans, but need not be near-optimal for the source, and near-optimal source plans need not have small defect. This is a characterisation of cost preservation, not a proof that such plans exist, and it does not say that the defect of any single plan equals the difference of costs.

Status records a written deduction, not independent validation.
