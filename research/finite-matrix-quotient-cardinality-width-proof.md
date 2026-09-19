---
rg: 2
id: finite-matrix-quotient-cardinality-width-proof
kind: route
title: Bound each finite unitary factor by the continuum and take the product
target: finite-matrix-quotient-cardinality-width-bound
requires: []
---

For finite `d`, the matrix algebra `M_d(C)` is `C^(d^2)` as a set, so it has
cardinality `continuum`; therefore `|U(d)|<=continuum`.  Hence

```text
|product_(j in J) U(d_j)| <= continuum^|J|.
```

A quotient set cannot have larger cardinality than its source.  An injective
image cannot have larger cardinality than its codomain, proving `(WID1)` and
the embedding obstruction.

