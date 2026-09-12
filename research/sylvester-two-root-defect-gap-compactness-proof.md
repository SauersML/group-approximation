---
rg: 2
id: sylvester-two-root-defect-gap-compactness-proof
kind: route
title: The space of Sylvester rank functions is compact, and a defect-killing limit is the augmentation rank
target: sylvester-rank-functions-have-a-uniform-two-root-defect-gap
requires:
  - corner-defect-killing-rank-functions-are-augmentation
  - binary-leavitt-unit-group-four-generated
  - leavitt-cylinder-swaps-generate-thompson-in-el
artifacts:
  - research/artifacts/rank-gate-axiom-audit-2026-09-12.md
---

Artifact Proposition 4.1.

1. **One number.** Prefix-replacement units in `V <= R^x` conjugate `iota_A` to `iota_B` for proper
   prefixes, so `rk(iota_P(D))` does not depend on `P`.
2. **Compactness.** The Sylvester axioms are closed conditions on bounded values, so the rank functions
   form a compact subset of a product of intervals, and evaluation at a matrix is continuous.
3. **Limit.** A sequence with displacement at least `eta` at a fixed generator and corner defect tending
   to `0` has a limit point with displacement at least `eta` and corner defect `0`. By
   `corner-defect-killing-rank-functions-are-augmentation` it is the augmentation rank, which moves no
   generator. Contradiction.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 18.4 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
