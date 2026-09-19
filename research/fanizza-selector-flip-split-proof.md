---
rg: 2
id: fanizza-selector-flip-split-proof
kind: route
title: Covariantize over the incidence gauge group and tensor the stationary S4 and D8 factors
target: fanizza-selector-flips-split-from-native-triangle
requires:
  - gauge-doubling-gives-selector-flip-symmetries
  - fanizza-reflection-recurrence-has-s4-stationary-overlap
  - flat-fanizza-triangle-realizes-every-separator-distribution
artifacts:
  - research/artifacts/fanizza-selector-flip-split-cell-audit-2026-08-21.md
---

Gauge covariantization gives `(SFS1)--(SFS3)`: selector flips are implemented
exactly, while their implementers commute with every invariant logical word.
In the finite `S_4` model, decompose the three commuting triangle separators
into their joint character spaces.  The third prerequisite extends every
separator character to the private variables of all triangle contexts, so
these extensions may be installed fiberwise without changing the `S_4`
recurrence.  Covariantize this combined packet and tensor an independent D8
canonical mixture with `tr(H)=1/8`.

All listed relations act on their designated tensor factors and hence hold
exactly.  The positive D8 holonomy is unchanged.  If those relations implied
a trace-cyclic proper return, finite-dimensional trace cyclicity would force
`tr(H)=0`, contradicting the explicit tensor model.
