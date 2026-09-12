---
rg: 2
id: audit-kl-gate-times-cyclic-pure-root
kind: route
title: Canonicalize every KL-gate/pure-root product and read the identity fiber
target: kl-gate-times-pure-root-has-identity-fiber-obstruction
requires:
  - canonical-left-comb-kl-gate-is-a-mixed-involution
  - two-kl-gate-orbit-has-identity-fiber-obstruction
  - inverse-packet-conjugator-must-mix-s-and-t-charts
artifacts:
  - research/artifacts/kl-gate-in-c3-corner-chart-2026-08-21.md
  - research/artifacts/verify-kl-gate-c3-corner.py
---

Transport `x_12(s_0)` and `x_12(t_1)` through the same left-comb prefix
equivalence and generate their twenty coordinate-cycle conjugates.  For both
orders with each mixed gate, use the reverse word as the inverse, expand the
three packet-correction summands, and canonicalize every unit by the Bergman
rule.  All 1,600 audits have correction-bit triple `(0,0,0)` against the base
identity bit one.
