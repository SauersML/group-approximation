---
rg: 2
id: s3-endpoint-global-cell-necessity-proof
kind: route
title: Conjugate the reset commutators back and expand the compressed covariance row
target: s3-endpoints-need-capacity-gated-global-cell
requires:
  - two-raw-radicals-fail-common-symplectic-reset
  - regular-clifford-edge-map-has-zero-kernel
  - global-covariance-misses-capacity-compression
---

If `(EGC1)` placed both endpoint words in the commutant of the fresh reset
image, conjugation by `t^(-1)` would place both raw endpoint words in the old
reset commutant.  Equation `(RRC4)` says that commutant contains only their
sum, proving the first obstruction.

The second obstruction is the normal-form kernel computation
`(RCK7)--(RCK9)`: private regular factors give an injective semidirect map,
while identifying their residual `p,q` coordinates kills all pairwise factor
differences and has kernel dimension `150`.

For the only remaining type of attachment, multiply an unconditional
covariance relation by the common source projection `Q` and insert
`vZQ-vQZ`.  This gives `(EGC3)`.  The example `v=I`, `a=Z`, with `Q` not
reducing `Z`, has zero global covariance defect and positive compressed
defect.  Hence the missing term must be named and paid by a mixed
capacity-gated cell.  These three alternatives exhaust the stable-edge,
literal-sharing, and uncompressed-global shortcuts claimed in the statement.
