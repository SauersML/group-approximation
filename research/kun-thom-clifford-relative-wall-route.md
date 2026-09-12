---
rg: 2
id: kun-thom-clifford-relative-wall-route
kind: route
title: Use a finite Clifford wall instead of embedding the whole crossed product
target: hyperlinear-nonsofic-group
requires: [kun-thom-clifford-radical-phase, kun-thom-clifford-relative-wall]
artifacts:
  - notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md
  - GroupApproximation/Sofic/CliffordPhaseExtraction.lean
  - GroupApproximation/Sofic/AntipodalRadicalCollision.lean
---

The relative wall defines a tracial-ultraproduct image of the Kun--Thom
free-lamp group in which the sofic-radical word converges to `-1`.  The
kernel-checked antipodal radical-collision theorem makes that image
hyperlinear and nonsofic.  No faithful model of the whole crossed product is
required.
