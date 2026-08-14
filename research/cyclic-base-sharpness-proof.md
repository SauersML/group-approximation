---
rg: 2
id: cyclic-base-sharpness-proof
kind: route
title: Separate finite-dimensional invisibility from MF invisibility
target: cyclic-base-sharpness
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Monsters/LiteralCyclicCalibration.lean
  - GroupApproximation/Monsters/CyclicBaseLEFObstruction.lean
---

## Direct proof

Finite-dimensional commutant dimension makes the cyclic compression defect
vanish in every exact model.  Nevertheless the explicit Clifford quotient
maps its square to the nontrivial sign.  That quotient is locally-finite by
the solvable affine group `BS(1,2)`, hence amenable and MF.  Its faithful MF
model detects the sign.  The same quotient is neither residually finite nor
LEF, showing why exact finite models cannot supply the detector.
