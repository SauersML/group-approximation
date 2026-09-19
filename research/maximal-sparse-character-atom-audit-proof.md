---
rg: 2
id: maximal-sparse-character-atom-audit-proof
kind: route
title: Compare global corona atoms with coordinate exact joint-character atoms
target: maximal-sparse-character-atom-does-not-return-multiplicity
requires:
  - norm-corona-sparse-global-character-atom
  - leavitt-heisenberg-branch-doubles-character-multiplicity
  - leavitt-character-mass-escapes-to-finer-characters
  - finite-branch-closure-erases-transverse-character
---

Apply the branch and shear to the sparse atom in the quotient.  Their fixed
coefficient eigenrelations hold there and give the larger returned corona
atom.  At a coordinate, however, only each fixed coefficient relation tends
to zero; the coefficient witnessing a split may move with the coordinate.
The exact commuting lift therefore refines the returned range into moving
extensions of the same finite-window character.  This is exactly the marginal
escape recorded by the required claims, and branch-closing a fixed window
removes the transverse direction.  Coordinatewise maximal rank consequently
cannot be applied to the returned projection.

