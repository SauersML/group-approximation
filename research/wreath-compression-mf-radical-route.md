---
rg: 2
id: wreath-compression-mf-radical-route
kind: route
title: Collapse plus reduction theorem plus RF quotient
target: wreath-compression-mf-radical
requires:
  - compression-torsion-collapse
  - doubling-quotient-residually-finite
artifacts:
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
  - GroupApproximation/Sofic/TorsionCompressionCollapse.lean
---

Torsion collapse along all powers of the stable letter globalizes to the
expansion subgroup (kernel-checked propagation); two-point fibers force
fiberwise abelianization (kernel-checked); the kernel-checked reduction
theorem actualCoronaMFResidual_eq_comap_quotient plus the RF quotient
computes the radical exactly.
