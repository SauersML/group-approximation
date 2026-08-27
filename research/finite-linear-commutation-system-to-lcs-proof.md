---
rg: 2
id: finite-linear-commutation-system-to-lcs-proof
kind: route
title: Enforce each desired commutator with one three-variable parity row
target: finite-linear-commutation-system-to-lcs
requires: []
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
---

For each required commuting pair `u,v`, the added LCS row
`u+v+a_(u,v)=0` has operator relations saying that its three involutions
commute and their product is one.  Hence every LCS solution restricts to
`uv=vu`, with `a_(u,v)=uv`.  Conversely, commuting involutions `u,v` have
`uv` again an involution commuting with both, so assigning
`a_(u,v)=uv` satisfies the row exactly.  The original affine equations are
unchanged LCS rows.  Applying this independently to the finitely many pairs
proves the claimed perfect-solution equivalence.
