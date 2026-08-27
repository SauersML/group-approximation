---
rg: 2
id: atlas-repeated-h6-gauge-coordinate-proof
kind: route
title: Split the natural module into two trivial lines and one simple S3 plane
target: atlas-repeated-h6-gauge-is-one-gl2m-coordinate
requires: []
---

In the literal H6 labels, coordinates zero and three are fixed pointwise and
coordinates one and two carry the irreducible natural two-dimensional S3
module `W`.  Hence

```text
V restricted to H6 = 1^2 direct_sum W.
```

There are no H6 maps between the trivial and `W` blocks, and
`End_H6(W)=F2`.  Tensoring by `M` gives the algebra
`Mat_(2m)(F2) direct_sum Mat_m(F2)` and therefore `(RHG1)` on units.
Absolute irreducibility of the natural A8 module gives `(RHG2)` by Schur.

Write an H6 gauge as `(A,B)`.  Left multiplication by the full-chart gauge
`D=B^-1` sends it uniquely to `((I_2 tensor B^-1)A,I)`.  This identifies the
coset space with `GL_(2m)(2)` and proves `(RHG3)`.
