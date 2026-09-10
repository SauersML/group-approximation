---
rg: 2
id: fpbs-dead-local-pivotal-charging
kind: route
title: Charge the near-critical pivotal budget locally along the walk path
target: fpbs-pivotal-budget-universal
requires: []
artifacts:
  - research/artifacts/fpbs/exploration-pivotal-projections.md
  - research/artifacts/fpbs/responses/08_0908-205457.md
---

Dead: the naive charging rule bounds the conditional pivotal count for a long connection by summing the counts of adjacent steps, which needs a triangle inequality for conditional expected pivotal counts and a uniform bound at adjacent pairs. Both fail. An exact six-cycle defect transferred to C6 * C2 refutes the triangle inequality (fpbs-pivotal-triangle-fails), and degree-three networks have adjacent terminals with pivotal counts growing linearly in depth (fpbs-hierarchical-pivotal-amplification). Purely local bounds are therefore unavailable; the universal budget is not refuted by either counterexample.
