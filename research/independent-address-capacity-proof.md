---
rg: 2
id: independent-address-capacity-proof
kind: route
title: Sum the normalized dimensions of disjoint address cylinders
target: independent-address-capacity-cannot-drive-selected-atom-growth
requires: []
---

An affine cylinder of codimension `c` in `F_2^D` has exactly `2^(D-c)`
points.  Pairwise disjointness therefore gives

```text
sum_i 2^(D-c_i)<=2^D,
```

which is `(IAC1)` after division by `2^D`.  For a general finite-dimensional
address algebra, orthogonality gives `sum_i R_i<=1`; multiply by the
commuting payload projection and apply the normalized trace to obtain
`(IAC2)`.  Both calculations are exact and dimension independent.
