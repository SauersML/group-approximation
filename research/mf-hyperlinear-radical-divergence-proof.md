---
rg: 2
id: mf-hyperlinear-radical-divergence-proof
kind: route
title: Combine corona invisibility with the Clifford CE detector
target: mf-hyperlinear-radical-divergence
requires: [literal-central-mark-corona-invisible, literal-clifford-ce-model]
artifacts:
  - GroupApproximation/Sofic/RadicalSeparation.lean
  - notes/NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md
---

The operator-norm theorem places `w` in the MF residual.  The explicit
Connes-embeddable detector sends `w` to `-1`, excluding it from the
hyperlinear residual.  The elementwise implication is formalized as
`not_coronaMFResidual_le_hyperlinearResidual_of_detector`.
