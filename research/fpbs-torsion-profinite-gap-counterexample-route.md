---
rg: 2
id: fpbs-torsion-profinite-gap-counterexample-route
kind: route
title: A cheap action of a positive-gradient residually finite torsion group undercuts every profinite action
target: fpbs-fixed-price-counterexample-exists
requires:
  - fpbs-positive-gradient-torsion-group-cheap-action
  - fpbs-abert-nikolov-rank-gradient-equals-profinite-cost
artifacts:
  - research/artifacts/fpbs/counterexample-heretic-w5-2026-09-17.md
---

- **Chain.** `Q` is countable and residually finite, so it has a normal chain
  with trivial intersection. That chain is Farber.
- **Expensive side.** Each term of the gradient is at least `RG(Q)`, so
  Abert--Nikolov gives a free action of cost at least `1 + RG(Q)`.
- **Cheap side.** The claimed action costs less than `1 + RG(Q)`.

The two actions have different costs.
