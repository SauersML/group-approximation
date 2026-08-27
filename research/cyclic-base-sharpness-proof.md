---
rg: 2
id: cyclic-base-sharpness-proof
kind: route
title: Separate finite-dimensional invisibility from MF invisibility
target: cyclic-base-sharpness
requires: [amenable-implies-operator-mf]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Monsters/LiteralCyclicCalibration.lean
  - GroupApproximation/Monsters/CyclicBaseLEFObstruction.lean
---

## Proof

Finite-dimensional commutant dimension makes the cyclic compression defect
vanish in every exact model.  Nevertheless the explicit Clifford quotient
maps its square to the nontrivial sign.  That quotient is locally-finite by
the solvable affine group `BS(1,2)`, hence amenable and MF.  Its faithful MF
model detects the sign.  The same quotient is neither residually finite nor
LEF, showing why exact finite models cannot supply the detector.

## Why this is not `requires: []`

It was, until 2026-08-16.  The step "hence amenable **and MF**" is the one
place in this route that no in-repo theorem reaches: the quotient is amenable
but neither residually finite nor LEF, and by
[[permutation-norm-models-certify-exactly-lef]] every MF certificate the
repository has factors through exact finite models, which provably cannot
certify a non-LEF group.  So the detector rests on
[[amenable-implies-operator-mf]] — a published theorem the development does not
have — and the prerequisite records that rather than hiding it inside a
`requires: []` commitment.  Nothing downstream is affected: no route requires
this target and it invalidates nothing.  Everything else in the route,
including the failure of residual finiteness and of LEF, is machine-checked in
the two cited modules.
