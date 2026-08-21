---
rg: 2
id: s3-active-return-via-three-channel-holonomy
kind: route
title: Replace nonlinear scalar return by three equal-scale affine channels and one multiplicity two-cell
target: s3-active-packet-proper-corner-return
requires:
  - s3-active-complement-is-three-equal-scale-affine-atoms
  - s3-affine-hnn-transports-the-active-vector
  - packet-central-active-complement-reduces-shared-words
  - s3-three-channel-multiplicity-holonomy
  - finite-schur-clifford-packet-flexible-hs-exactification
  - context-local-schur-packet-marked-extension
---

Split the analytic complement into the three atoms `(SEA2)`.  Their common
spin scale turns Hilbert-rank transport into exactly the required weighted
multiplicity transport.  The affine HNN chart gives the fixed
`O(sqrt(E))` local comparison without naming the union and without
globalizing any original context selector.  The reducing-corner theorem
controls every shared BCS word on their orthogonal sum.

Apply the nonstationary multiplicity two-cell only to the resulting three
external coordinates.  Its exit clause retains `P_(-,-)` in the first-hit
reservoir, and its properly infinite clause extends the marked witness.
These are precisely the five obligations of the target.  The route does not
credit the ordinary HNN edge with contraction; all strictness is isolated in
the new holonomy claim.
