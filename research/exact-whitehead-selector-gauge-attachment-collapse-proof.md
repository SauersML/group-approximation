---
rg: 2
id: exact-whitehead-selector-gauge-attachment-collapse-proof
kind: route
title: Apply the two affine selector equations in the canonical packet corner
target: exact-whitehead-selector-gauge-attachment-collapses-packet
requires:
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
---

Because `B` is finite and embedded, restriction of the canonical group
trace to `C[B]` is the regular trace.  The central isotypic projection of a
`d`-dimensional irreducible therefore has trace `d^2/|B|`, proving `(EWS1)`.

Normalize the trace on the nonzero corner `eL(Gamma)e`.  Exact conjugacy of
the two multiplicity involutions makes their positive spectral fractions
equal to one number `theta`.  Apply `(TSG1)--(TSG2)` to the two exact rows in
`(EWS3)`.  For `(r,q)=(1/2,1/4)` one obtains `theta=1/2`; for
`(r,q)=(1/4,1/8)` one obtains `theta=5/6`.  Hence the corner cannot be
nonzero.  Faithfulness of the canonical trace gives `e=0`, contradicting
`(EWS1)`.
