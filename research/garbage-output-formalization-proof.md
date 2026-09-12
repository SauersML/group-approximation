---
rg: 2
id: garbage-output-formalization-proof
kind: route
title: Output the Bennett remainder on an extra track and add it back in the left inverse
target: garbage-output-tracks-formalize-every-left-inverse-pair
requires: []
artifacts:
  - research/artifacts/stable-formalization-erasure-audit-2026-09-12.md
---

Section 1 of the artifact.
- **The remainder vanishes on points.** `d` vanishes on points because `σ ∘ τ = id`, so the second
  output is `0` on points.
- **Formal identity.** `σ~(τ~(X)) + d(X) = X` holds as polynomials.
- **No constraint.** The Jacobians at a constant configuration are an `n × 2n` matrix and a
  `2n × n` matrix with product `I_n`, such as `[I 0]` and `[I; 0]`. Direct finiteness says nothing
  about such pairs.
