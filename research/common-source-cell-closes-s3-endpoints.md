---
rg: 2
id: common-source-cell-closes-s3-endpoints
kind: route
title: Specialize the capacity-gated common-source cell to the three S3 endpoint contexts
target: s3-equivariant-endpoint-conventions-use-global-bcs-words
requires:
  - regular-induced-affine-reset-synchronizes-s3-holonomy
  - regular-clifford-edge-map-has-zero-kernel
  - gauge-doubling-gives-selector-flip-symmetries
  - capacity-gated-s3-endpoint-common-source-cell
  - common-source-covariance-locks-binary-marginals
---

Use the private regular edge to synchronize the three reset transports while
retaining the original logical BCS words.  Apply `(SEC1)--(SEC2)` to the three
endpoint contexts `00,01,11`, using the original shared logical words
`Z_X,Z_Y` for their two common endpoints.

The endpoint cell gives the same source Gram `Q` for all three rows.  Equations
`(CSM2)--(CSM3)` therefore identify the `X` marginals of `00,01` and the `Y`
marginals of `01,11` with total error `O(sqrt(E_rel))`.  Its target residual
terms `(SEC3)` are the two diagonal and one crossed failure projections, so
`(CSM4)` and `(SEC4)` bound convention failure by the same energy.  The source
commutator terms in `(SEC4)` ensure these are compressed events of the shared
BCS words rather than context-private copies.

Gauge doubling fixes `Z_X,Z_Y` and the native mark while all private shares
and residual factors remain private, as required by the zero-kernel audit.
On the exact HALT witness the forbidden source `Q` vanishes, so every
capacity-gated row is zero and the attachment extends after the already
allowed countable amplification.  These are precisely the finite-matrix and
exact-completeness clauses of the target endpoint claim.
