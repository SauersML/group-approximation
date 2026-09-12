---
rg: 2
id: fpbs-traffic-variational-cost-identities
kind: claim
title: Finite routing plans give exact variational formulas for both action costs
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/docs/finite-fiber-cost-descent.md
  - research/artifacts/fpbs/responses/51_0909-211602.md
---

For any free factor pi:Y->X of actions of a countably infinite group with
C(X)<infinity, fix a finite-cost generating base graphing Lambda. Use finite
prefix routing plans whose repair budgets include the complete demand-tail
cost, as in Section 9 of the artifact. With the notation of the descent bound,
over all such plans on Y (allowing the prefix to increase),

C(Y) = inf B,    C(X) = inf (B + J_pi),    so   C(X) - C(Y) = inf [ (B - C(Y)) + J_pi ],

with both bracketed terms nonnegative. Hence C(X) = C(Y) exactly when there are plans with B tending to C(Y) and J_pi tending to 0 simultaneously. The simultaneity is the whole content: plans with zero defect always exist by lifting target plans, but need not be near-optimal for the source, and near-optimal source plans need not have small defect. This is a characterisation of cost preservation, not a proof that such plans exist, and it does not say that the defect of any single plan equals the difference of costs.

Finite generation is not required. The finite-cost base hypothesis supplies
a summable ordinary repair budget and also ensures C(Y)<=C(X)<infinity.
For a uniform q-point free factor, finite source cost already ensures
finite base cost by `fpbs-finite-fiber-cost-bound`, so these identities
apply under that sufficient hypothesis as well. The same input proves
this for an ergodic base with an atomic part in the conditional
measures and finite source cost. The identities do not exclude
finite-cost sources over infinite-cost bases with arbitrary fibers or
prove universal vanishing of the defect.

Section 10 also proves continuity along increasing information factors:
if X is a finite-cost base, Y->Z_r->X, their invariant sigma-algebras
increase and generate that of Y, then C(Z_r) decreases to C(Y).
Equality with C(X) still requires cost preservation at the stages.

Status records a written deduction, not independent validation.
