---
rg: 2
id: stw81-ctdim-morita-correspondence-proof
kind: route
title: Transport continuous-trace subquotients through the Rieffel ideal correspondence
target: stw81-ctdim-morita-invariance
requires:
  - stw81-continuous-trace-shadow-invariant
artifacts:
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
---

A strong Morita equivalence between `A` and `B` induces the Rieffel lattice
isomorphism between their ideals.  It preserves inclusions and transports
every subquotient `J/I` of `A` to a strongly Morita equivalent subquotient
of `B`; applying the inverse equivalence gives a bijection in the other
direction.

Continuous trace is Morita invariant, and strongly Morita equivalent
algebras have homeomorphic primitive ideal spaces.  The corresponding
continuous-trace subquotients therefore have identical spectrum dimensions.
Taking suprema proves `ctdim(A)=ctdim(B)`.

By `stw81-continuous-trace-shadow-invariant`, for separable algebras the
LXXXI shadow hypothesis is exactly `ctdim<=1`, proving its Morita
invariance.  The stabilization statement follows from the standard Morita
equivalence between `A` and `A tensor K`.
