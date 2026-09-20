---
rg: 2
id: polynomial-valuation-germ-towers-are-f-infinity
kind: claim
title: Polynomial valuation germ full groups and all finite rational marked stabilizers have type F_infinity
artifacts:
  - research/artifacts/polynomial-germ-unitriangular-manuscript-2026-09-20.md
---

**OPEN — conditional on the unresolved affine base and polynomial induction.**

For every `m≥2,q≥2,p∤q`, `d≥0`, and `r≥1`, the full group `B_{d,r}`
of artifact §§6–7 and every pointwise or setwise stabilizer of a finite
subset of its rational marked set have type `F_∞`.

## Attempts

The proposed proof is simultaneous induction on polynomial degree,
including all finite marked stabilizers at every stage. The affine base
uses a commuting ascending HNN presentation. The successor stage uses
the normal germ quotient `J_d/J_{d-1}≅Z`, then repeats BHM on a punctured
space to establish the next stabilizers. These are separate open claims;
the conditional induction route records their exact role. Formula checks
verify neither base nor induction step. No Lean theorem establishes this
statement yet.
