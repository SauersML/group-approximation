---
rg: 2
id: fpbs-cost-one-backbone-fixes-completion-bill
kind: claim
title: A cost-one aperiodic subrelation makes the optimal completion bill exactly the excess cost
distinct_from:
  fpbs-amen2-cost-inputs: that bundles the amenable cost facts and imports only the one-sided bound relC(R;S) <= C(R)-1; this one is the two-sided consequence for a cost-one aperiodic subrelation together with the sandwich for near-cost-one subrelations
  fpbs-normalized-cost-induction-input: that is the complete-section induction formula itself; this one is the relative-cost statement deduced from it
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/responses/51_0909-211602.md
---

For an orbit relation R and an aperiodic subrelation H contained in R with C(H) = 1, the relative cost is relC(R;H) = C(R) - 1. Consequently no choice of cost-one backbone changes the optimal completion bill: a cleverer backbone can make a good construction easier to find, but the remaining bill is C(R) - 1 in every case. More generally, if C(H_t) = 1 + t then max(0, C(R) - 1 - t) <= relC(R;H_t) <= C(R) - 1, so the optimal completion costs of near-cost-one starting relations tend to C(R) - 1. Effort should therefore go to the completion cost and its behaviour under forgetting information, not to lowering the starting cost.

Status records a written deduction from an imported theorem, not independent validation.
