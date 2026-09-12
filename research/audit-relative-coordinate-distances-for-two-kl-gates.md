---
rg: 2
id: audit-relative-coordinate-distances-for-two-kl-gates
kind: route
title: Audit the identity fiber for every ordered pair of coordinate KL gates
target: two-kl-gate-orbit-has-identity-fiber-obstruction
requires:
  - canonical-left-comb-kl-gate-is-a-mixed-involution
  - kl-gate-corner-test-is-an-even-unit-fiber-audit
  - both-rank-three-factors-must-be-packet-corrected
artifacts:
  - research/artifacts/kl-gate-in-c3-corner-chart-2026-08-21.md
  - research/artifacts/verify-kl-gate-c3-corner.py
---

Write the inverse-pair defect as the base term `Delta` plus its two linear
packet terms and one bilinear packet term.  First audit the nineteen anchored
words `q_0q_d`, then audit all 380 ordered pairs because the fixed corner
lifts need not share the apparent cyclic symmetry.  Canonicalize every
Leavitt unit in the four summands and read only the identity fiber.  The base
bit is one and all three correction bits vanish for every ordered pair.
