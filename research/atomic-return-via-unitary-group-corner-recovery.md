---
rg: 2
id: atomic-return-via-unitary-group-corner-recovery
kind: route
title: Import a properly infinite corner decomposition through the abstract unitary group
target: binary-leavitt-atomic-morita-return
requires:
  - properly-infinite-cstar-quotient-is-compatible-with-fp-mf-group
  - unitary-group-embedding-recovers-the-corner-decomposition
---

Work in a properly infinite operator algebra, where the Cuntz isometries
supply exactly the two inverse rows and the completeness row the atomic
return asks for.  Embed the unitary group of that algebra into finite
matrices, transport the reflections of its range projections, and read the
three coefficient rows off the transported corner.  The route needs no
coefficient-ring representation and no spectral estimate: only that the
embedding is injective, unital and scalar preserving.

This route is invalid.  Those hypotheses do not transport the projection
lattice.  By
`unitary-embedding-does-not-preserve-corner-orthogonality`, the induced map
on projections can turn two orthogonal rank-one projections into commuting
rank-13 projections with a rank-6 product, and can fail additivity with
error of operator norm 2, so the transported family satisfies neither an
inverse row nor a completeness row.
