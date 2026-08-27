---
rg: 2
id: kun-thom-clifford-radical-phase-proof
kind: route
title: Combine centralizer normalization with two-Majorana anticommutation
target: kun-thom-clifford-radical-phase
requires: []
artifacts:
  - notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md
  - GroupApproximation/Sofic/CliffordLampGroup.lean
  - GroupApproximation/Sofic/CliffordPhaseExtraction.lean
  - GroupApproximation/Sofic/AntipodalRadicalCollision.lean
---

The conjugate `t r t^(-1)=[tkt^(-1),gamma]` is killed by every homomorphism
to a sofic group, so normality of the sofic radical contains `r` and `x`.
The cosets `Gamma` and `hGamma` are distinct.  Their Majoranas anticommute,
and the elementary commutator calculation sends `x` exactly to the central
scalar `-1`.  The algebraic phase extraction and radical-collision endpoint
are checked in the cited Lean modules.
