---
rg: 2
id: compressed-k2m-capacity-proof
kind: route
title: Synchronize the rectangle gauges and apply one orthogonal-source capacity bound
target: compressed-k2m-locks-gauge-but-needs-matrix-separator
requires:
  - unitary-k2m-rectangle-synchronization
  - eight-slice-bookkeeping-symmetrizes-s3-failures
  - one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum
---

Use exact `K_(2,m)` row-column synchronization to replace every row-one edge
by one common row gauge times its column gauge, with squared error exactly the
sum of rectangle holonomies. The row-zero orthogonality makes the transported
source sum a projection. Its leakage outside a capacity projection is at
least source trace minus capacity trace. A Hilbert-direct-sum triangle
inequality gives `(CKR6)`. Exact row-column factorizations show rectangles
alone have zero energy; the regular trace rules out promoting the compressed
leakage bound to universal reflection relators.
