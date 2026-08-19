---
rg: 2
id: compression-torsion-collapse
kind: claim
title: Pointwise compression-torsion collapse in norm matrix coronas
artifacts:
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
  - GroupApproximation/Sofic/TorsionSpectralCollapse.lean
---

Let W be countable, pi a norm-corona representation, Lambda <= W Kazhdan,
s a one-sided compressor of Lambda, and k an element whose image has
finite order, whose Lambda-orbit images pairwise commute, and which pi
identifies with its s Lambda s^{-1}-conjugates.  Then pi identifies k with
its entire Lambda-conjugation orbit.  Group-theoretic globalization
(expansion closure, fiber abelianization, radical reduction) is
kernel-checked in GroupApproximation/Sofic/TorsionCompressionCollapse.lean,
and the collapse gate itself is discharged unconditionally at every
finite order by the Fourier-idempotent reduction to the projection
collapse (GroupApproximation/Sofic/TorsionSpectralCollapse.lean).
