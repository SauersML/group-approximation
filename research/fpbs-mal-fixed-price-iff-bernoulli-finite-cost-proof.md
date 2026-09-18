---
rg: 2
id: fpbs-mal-fixed-price-iff-bernoulli-finite-cost-proof
kind: route
title: Bound every free action's cost by the Bernoulli cost, then close with the c-star-or-infinity dichotomy and the stage-shift dichotomy
target: fpbs-mal-fixed-price-iff-bernoulli-finite-cost
requires:
  - fpbs-finite-cost-transfers-up-weak-containment
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - fpbs-shifted-stage-relative-cost-zero-or-infinite
  - fpbs-locally-free-free-action-costs-are-c-star-or-infinite
  - fpbs-mal-odometer-product-actions-have-cost-two
artifacts:
  - research/artifacts/fpbs-finite-cost-transfers-up-weak-containment-2026-09-18.md
---

Artifact §4, Corollary 4.

- **2 ⇔ 3 ⇔ 4 ⇔ 6.** `fpbs-shifted-stage-relative-cost-zero-or-infinite`
  gives `C(β) = 2` iff `relC(E_β; E_{β|H_1}) = 0`, and otherwise
  `C(β) = ∞`. Item 6 is the negation of the floor claim's statement.
- **2 ⇔ 5.** If `a` is free and `a ≼ β`, then `β ≼ a` by Abért–Weiss. By
  `fpbs-finite-cost-transfers-up-weak-containment` in both directions,
  `C(a) = C(β)`.
- **1 ⇒ 2.** `fpbs-mal-odometer-product-actions-have-cost-two` exhibits a
  free action of cost 2, so under fixed price `C(β) = 2`.
- **3 ⇒ 1.** By Abért–Weiss, `β ≼ a` for every free `a`. By
  `fpbs-finite-cost-transfers-up-weak-containment`, `C(a) ≤ C(β) = 2`. By
  `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`,
  `C(a) ∈ {c*, ∞}`, and `c* = 2` (odometer node, item 3). So `C(a) = 2`.
