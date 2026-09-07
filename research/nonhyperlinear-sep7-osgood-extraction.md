---
rg: 2
id: nonhyperlinear-sep7-osgood-extraction
kind: claim
title: An Osgood microscopic seed modulus suffices for flexible HS stability
artifacts:
  - research/artifacts/nonhyperlinear-sep7-osgood-extraction.md
distinct_from:
  sequential-exact-corner-extraction-has-quadratic-error-ledger: that sums errors for an already supplied finite extraction; this proves that an Osgood seed modulus keeps every residual admissible until a full correction is obtained.
  moving-subgroup-schreier-correction-has-no-index-loss: that gives a spectral-to-corner construction and uses a linear microscopic seed bound; this supplies a general nonlinear iteration theorem and allows a logarithmic loss in that seed bound.
---

For any fixed finite presentation with inverse-compatible tuples, let
`delta(U)` be its maximum normalized-HS defining-relator defect.
Let psi be continuous and nondecreasing near zero, with `psi(0)=0`,
`psi(t)>0` for positive t, and `integral_0 dt/psi(t)=infinity`.

Assume uniformly in dimension that every tuple with
`0<delta(U)<delta_*` has either a nonzero exact rank-r corner with
retained-column squared error at most `psi(delta(U)^2) r` in
unnormalized HS norm, or a full exact correction whose normalized
squared generator error and relative padding are both at most
`psi(delta(U)^2)`. The corner rank may be one.

Then the group is flexibly normalized-HS stable. In particular,
`psi(t)=K t log(e/t)` suffices. If ell is the longest relator length,
`C=6K ell^2`, and `L=log(e/delta(U)^2)`, this logarithmic hypothesis
gives generator error `O(L^(-1/(4C)))` and relative padding
`O(L^(-1/(2C)))` at sufficiently small defect.

This is an implication with an explicit seed hypothesis. It does not
assert that any arithmetic group has these seeds, and it does not
require property (T) or a prescribed limiting character. The proof
uses a finite number of cuts, at most the original matrix dimension.
