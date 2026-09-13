---
rg: 2
id: commuting-jordan-certificates-flatten-proof
kind: route
title: Induct on the power of x, removing each separated Frobenius step and reducing the Frobenius matrix by two elementary operations
target: commuting-jordan-certificates-flatten-to-minors
requires:
  - separated-triangular-steps-flatten-to-minors
artifacts:
  - research/artifacts/two-root-certificates-separate-2026-09-12.md
---

Artifact Section 3, Theorem 3.1 and Corollary 3.2.
- **Induction step.** `separated-triangular-steps-flatten-to-minors` with diagonal blocks `x^j P` (padding
  `P^((+)(j-1))`) and `xP`, and corner `P`.
- **Frobenius matrix.** `[[x^j P, P],[0, xP]] ~ P (+) x^(j+1) P` by one right and one left elementary
  operation, using `P x^j = x^j P`.
- **`K_0` reading.** An idempotent minor of an idempotent is dominated in `K_0`.
