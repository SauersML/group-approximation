---
rg: 2
id: two-bit-tag-routing-proof
kind: route
title: Transport the four endpoint atoms into one distinguished tag atom and its complement
target: two-bit-tag-routing-splits-s3-exit-and-survivor
requires:
  - s3-active-complement-is-three-equal-scale-affine-atoms
  - s3-affine-hnn-transports-the-active-vector
  - thompson-site-pulses-localize-hard-exits
  - point-stabilizer-local-hard-share-compiles-bridge-orbit
---

The four endpoint projections and the four tag projections are the minimal
idempotents of two copies of the same marked elementary-abelian table.
Choose the affine table isomorphism sending the endpoint `(-,-)` atom to the
tag `(-,-)` atom.  Conjugation by its bridge sends the other three atoms
bijectively onto the complement of that tag atom.

Because the bridge commutes with every earlier site tag, `R_n<=C_n` implies
`u_nR_nu_n^*<=C_n`.  Multiplying the exit image by `C_n` gives `X_n`; multiplying
the sum of the other three images by `C_n` gives `C_nS_n=C_(n+1)`.  The
telescope `C_(n+1)=C_n-X_n` proves orthogonality and the trace budget.

For the approximate statement, use the degree-two formulas for the four
minimal projections.  Replacing either of the two transported involutions
costs half its covariance defect.  Moving the bridge through the earlier
prefix costs the sum of the earlier tag commutator defects, and source-prefix
leakage contributes once to each of the two terms.  This yields `(TBT5)`.
