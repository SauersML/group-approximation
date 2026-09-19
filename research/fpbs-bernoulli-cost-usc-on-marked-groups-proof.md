---
rg: 2
id: fpbs-bernoulli-cost-usc-on-marked-groups-proof
kind: route
title: Approximate a near-optimal graphing by a finite cylinder certificate, patch disconnections with generator edges, and transfer on the agreement ball
target: fpbs-bernoulli-cost-usc-on-marked-groups
requires: []
artifacts:
  - research/artifacts/fpbs-marked-group-cost-limits-2026-09-19.md
---

Artifact, Section 1, Steps 1 to 3. The proof is self-contained, using measure-algebra density of cylinder sets and
countable additivity.

- **Step 1.** Locality of the certificate cost. The measure of a finite Boolean combination of i.i.d. coordinate
  conditions depends only on the equality pattern of the finitely many words involved.
- **Step 2.** Certificates compute `C(b_G)`. Split a near-optimal graphing into group-element pieces, truncate to
  finitely many, and bound the route event `E_s`. The perturbation is at most `2|D|m delta`.
- **Step 3.** Apply the certificate to `G_n` once `N_n cap B_(R(Z)) = N cap B_(R(Z))`.

Status records a written deduction, not formal verification.
