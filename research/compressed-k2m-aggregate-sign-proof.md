---
rg: 2
id: compressed-k2m-aggregate-sign-proof
kind: route
title: Aggregate the orthogonal sources and apply the hard-sign transport identity
target: compressed-k2m-deficit-is-one-aggregate-sign-row
requires:
  - unitary-k2m-rectangle-synchronization
  - hard-sign-transport-captures-exit-mass
---

Use the row-column factorization from
`unitary-k2m-rectangle-synchronization`.  Since
`B_jG_j=S_jB_j` and the row-zero source ranges are orthogonal,

```text
sum_j||(I-C)A_1B_jG_j||_2^2
 =sum_j||(I-C)A_1S_j||_2^2
 =||(I-C)A_1S||_2^2.
```

The capacity computation `(CKR8)` bounds the trace surplus by this quantity.
Apply `hard-sign-transport-captures-exit-mass` with source projection `S`,
source involution `R_S=I-2S`, target involution `R_C=I-2C`, and transport
`A_1`.  Its negative target projection is `C`, so it gives the middle
inequality of `(KAS3)`.  Right multiplication by `R_SA_1^*` turns the
additive covariance row into the displayed multiplicative word without
changing normalized Hilbert--Schmidt norm.
