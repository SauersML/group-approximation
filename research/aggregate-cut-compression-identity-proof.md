---
rg: 2
id: aggregate-cut-compression-identity-proof
kind: route
title: Expand a reflection in two-by-two blocks and retain contractions
target: aggregate-cut-compression-stores-boundary-as-involution-defect
requires:
  - regularized-anchor-square-function-has-dimension-free-cut
  - one-anchor-grading-makes-parity-damage-quadratic
---

Write `B_i` as a two-by-two operator matrix relative to `p+q`.  Its block
diagonal is `X_i`, and its block off-diagonal is `B_i-X_i`.  Expanding
`B_i^2=I` on the two diagonal corners gives `(ACS2)`.  Taking traces shows
that the sum of the two off-diagonal squared masses equals both
`tau(I-X_i^2)` and `||B_i-X_i||_2^2`.  The commutator `[p,B_i]` has the
same two off-diagonal blocks, with one sign changed, proving `(ACS3)`.

Because `p,q` commute with `A`, compression intertwines the anchor grading:
`qZ_iq=qY_iq`.  Kadison's compression inequality for the selfadjoint
operator `Y_i` gives `(qY_iq)^2<=qY_i^2q`; average to obtain `(ACS4)`.
The regularized cut supplies `(ACS5)`.  Finally telescope a length-`m`
word one occurrence at a time; all intermediate products are contractions,
and Cauchy--Schwarz proves `(ACS6)`.  The last sign-rounding estimate is the
scalar inequality `(sgn(lambda)-lambda)^2<=1-lambda^2` on `[-1,1]`.
