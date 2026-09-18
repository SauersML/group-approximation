---
rg: 2
id: fpbs-weakly-mixing-half-is-fixed-price-without-t-proof
kind: route
title: Apply P_w to the weakly mixing maximum times Bernoulli, then squeeze every free action by monotonicity and Bernoulli maximality
target: fpbs-weakly-mixing-half-is-fixed-price-without-t
requires:
  - burton-kechris-maximum-action-weakly-mixing-without-t
  - burton-kechris-cost-usc-and-maximum-action
  - weakly-mixing-fibre-products-are-relatively-weakly-mixing
  - fpbs-bernoulli-noise-does-not-change-cost
  - cost-is-constant-on-weak-equivalence-classes
  - fpbs-bernoulli-maximal-cost
artifacts:
  - research/artifacts/fpbs-weakly-mixing-half-is-fixed-price-2026-09-17.md
---

Artifact Section 3, Steps 1-5, together with Corollary C of Section 4.

- Step 1: a weakly mixing maximum a_w, from `burton-kechris-maximum-action-weakly-mixing-without-t`
  and the maximum of `burton-kechris-cost-usc-and-maximum-action`, item 2.
- Step 2: a_w is free, by upward closure of freeness (item 3 of the same node).
- Step 3: a_w × b → b is relatively weakly mixing, by
  `weakly-mixing-fibre-products-are-relatively-weakly-mixing`.
- Step 4: C(a_w × b) = C(a_w), by `fpbs-bernoulli-noise-does-not-change-cost`.
- Step 5: the squeeze, by `cost-is-constant-on-weak-equivalence-classes` and
  `fpbs-bernoulli-maximal-cost`.
