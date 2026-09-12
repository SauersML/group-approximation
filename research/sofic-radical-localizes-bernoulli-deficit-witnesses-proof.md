---
rg: 2
id: sofic-radical-localizes-bernoulli-deficit-witnesses-proof
kind: route
title: Count model-shift entropy on injective charts separated by product amplification
target: sofic-radical-localizes-bernoulli-deficit-witnesses
requires: [bernoulli-rokhlin-deficit-has-a-finitary-witness]
artifacts:
  - research/artifacts/bernoulli-deficit-witness-localization-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Section 1 of the artifact proves Theorem 1 there directly, in three steps:
- separating models built from the negation of invisibility;
- good points with injective charts;
- the entropy count `k|V| log q = H(Z) + H(x | Z)` along the model shift.

The prerequisite converts between deficits and configurations, which the consequences use.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 21 of the verification
artifact). The product amplification gives defect `<= r delta` and fixed fraction
`<= (1 - eps_0/|D|)^r`, and the count uses no sofic entropy theory.
