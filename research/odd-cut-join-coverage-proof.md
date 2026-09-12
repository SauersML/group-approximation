---
rg: 2
id: odd-cut-join-coverage-proof
kind: route
title: Join all anchor-invariant high cuts and reset their negative mass
target: join-of-odd-cuts-softens-an-entire-anchor-row
requires:
  - spectral-cut-anchor-reset-pays-boundary-in-one-row
  - odd-spectral-anchor-resets-have-monotone-sign-budget
---

The join of projections commuting with `A` commutes with `A`.  Orthogonality
to the join implies orthogonality to every individual high spectral
projection, proving `(JOC2)`.  Functional calculus of the reset gives
`(JOC3)` and telescoping decreasing negative projections gives `(JOC4)`.
Apply `(SAR4)` to isolate the join boundary.
