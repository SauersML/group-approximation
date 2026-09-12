---
rg: 2
id: nonhyperlinear-from-monomial-ce-kernel-face
kind: route
title: Quotient by a compact finite-phase CE-excluding face of the monomial extreme trace
target: non-hyperlinear-group
requires:
  - finite-phase-monomial-game-algebra-dictionary
  - toric-clause-spectra-cannot-generate-monomial-factor
  - monomial-finite-phase-ce-kernel-face-gap
  - ce-projective-kernel-face-gap-gives-nonhyperlinear-quotient
---

Use the finite-phase normal subgroup and character from
`monomial-finite-phase-ce-kernel-face-gap`.  Compactness extracts finitely
many graph relators.  Their normal closure is phase-safe, and the quotient is
finitely presented because the two-player question group is a finite direct
product of finite free products of cyclic groups.

The central defining-character corner of a hypothetical hyperlinear quotient
would pull back to a CE trace in the excluded face.  Therefore the quotient
is nonhyperlinear.  The factorial centrality theorem explains why the route
uses projective-kernel shadows rather than the monomial Fourier projections
as clause spectra.

