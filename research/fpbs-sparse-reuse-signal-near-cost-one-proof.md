---
rg: 2
id: fpbs-sparse-reuse-signal-near-cost-one-proof
kind: route
title: Reveal the reuse flags of a relative routing plan and bound their total measure
target: fpbs-sparse-reuse-signal-near-cost-one
requires:
  - fpbs-relative-traffic-descent-over-hyperfinite-spine
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
---

Section 6 of the artifact, Corollary D and the traffic warning that follows it. Given the relative descent formulas, choose a relative plan of budget below C(Y) - 1 + epsilon, reveal its flags, note that the relative traffic defect vanishes for the same two-case reason as in the absolute statement, and apply relC = C - 1 to convert the relative bound into C(Z) <= 1 + B_H. The measure bound is inclusion of each flag in its used domain, and the rarity statement is a union bound. The traffic inequality is Markov-free arithmetic from (N-1)_+ <= (K-1) times the indicator of reuse. This is a supplied deduction, not external validation.
