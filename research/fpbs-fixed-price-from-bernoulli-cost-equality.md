---
rg: 2
id: fpbs-fixed-price-from-bernoulli-cost-equality
kind: route
title: Sandwich every free action against a Bernoulli action, then pass to countable groups
target: fpbs-fixed-price-universal
requires:
  - fpbs-bernoulli-maximal-cost
  - fpbs-free-action-cost-at-least-bernoulli-cost
  - fpbs-fixed-price-countable-from-finitely-generated
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/responses/55_0909-215618.md
---

The honest decomposition of the goal as the reuse programme leaves it. For an infinite finitely generated group, Abert-Weiss gives C(a) <= C(b) for every free action a and a Bernoulli shift b, and the open reverse inequality gives C(a) >= C(b); together every free action has cost C(b), which is fixed price for that group. The third prerequisite carries the conclusion from finitely generated groups to all countably infinite ones, which the finite-routing arguments do not do on their own: they assume a finite generating set, finitely many demands, and finite costs.

This is a reduction, not a proof. Both the second and the third prerequisites are open, and the second is where the reuse programme actually stops.
