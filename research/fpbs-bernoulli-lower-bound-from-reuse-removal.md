---
rg: 2
id: fpbs-bernoulli-lower-bound-from-reuse-removal
kind: route
title: Get the Bernoulli lower bound from vanishing traffic defect on the product projection
target: fpbs-free-action-cost-at-least-bernoulli-cost
requires:
  - fpbs-correlated-reuse-flags-removable
  - fpbs-traffic-variational-cost-identities
  - fpbs-bernoulli-noise-does-not-change-cost
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
  - research/artifacts/fpbs/responses/55_0909-215618.md
---

Take a free action a and a Bernoulli shift b, and apply the variational criterion to pi from a x b onto b. Removability of the correlated reuse flags supplies plans with budget tending to C(a x b) and traffic defect tending to zero for that projection, so the criterion gives C(b) = C(a x b). Independent Bernoulli information is removable in the other projection, so C(a x b) = C(a). Hence C(a) = C(b), which contains the asserted inequality. All three inputs are for finitely generated groups, which is the scope of the target claim.
