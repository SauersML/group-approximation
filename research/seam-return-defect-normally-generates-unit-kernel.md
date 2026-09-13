---
rg: 2
id: seam-return-defect-normally-generates-unit-kernel
kind: route
title: Endpoint stable finiteness puts the return defect in the simple finitary kernel and determines the exact radical
target: aperiodic-seam-mf-radical-is-finitary-already-in-units
requires:
  - short-period-free-subshift-mf-dichotomy-reaches-unit-groups
  - heteroclinic-subshift-has-prescribed-mf-quotient
  - three-torsion-kazhdan-seam-is-just-non-mf
  - unit-idempotent-elementary-group-has-three-torsion-generators
artifacts:
  - research/artifacts/pestov91-return-towers-lower-mf-rank-2026-09-13.md
---

Section 4 notes that all seam points are aperiodic. The return-corner
defect vanishes in the stably finite endpoint rings, so its invisible
root or unit belongs to the finitary kernel. That kernel is infinite
simple, forcing it all into the MF radical; the LEF endpoint image
gives the reverse inclusion. The finite-block kernel calculation uses
only two outer colors. At rank three the original endpoint groups
are simple, and the same faithful-centralizer argument gives the five
normal subgroups. Applying the decoder separately to payload and phase
gives the four explicit torsion generators.
