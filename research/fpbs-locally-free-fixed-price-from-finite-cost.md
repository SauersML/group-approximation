---
rg: 2
id: fpbs-locally-free-fixed-price-from-finite-cost
kind: route
title: Finite cost of all free actions plus the c*-or-infinity dichotomy gives fixed price c* for locally free groups
target: fpbs-locally-free-groups-have-fixed-price
requires:
  - fpbs-locally-free-free-action-costs-are-c-star-or-infinite
  - fpbs-locally-free-free-actions-have-finite-cost
  - locally-free-groups-first-l2-betti-equals-c-star-minus-one
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

Let `Γ` be countably infinite and locally free.

- **Case `c* = ∞`.** By `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`,
  every free action has cost ∞. So `Γ` has fixed price `∞ = c*`.
- **Case `c* < ∞`.** By `fpbs-locally-free-free-actions-have-finite-cost`,
  every free action has finite cost. The dichotomy then gives cost `c*` for
  every free action, so `Γ` has fixed price `c*`.

In both cases `c* = 1 + beta_1^(2)(Γ)`, by
`locally-free-groups-first-l2-betti-equals-c-star-minus-one`.
