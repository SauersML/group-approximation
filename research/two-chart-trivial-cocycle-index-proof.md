---
rg: 2
id: two-chart-trivial-cocycle-index-proof
kind: route
title: Apply restriction-corestriction on each finite chart
target: two-chart-trivial-cocycle-order-divides-index-gcd
requires: []
---

For a subgroup `H<=G` and trivial circle coefficients, restriction followed
by corestriction acts on `H^2(G,T)` as multiplication by `[G:H]`.  If the
restriction of `[omega]` to `H` is zero, then

```text
[G:H] [omega]=0.                                      (BTCP1)
```

Apply `(BTCP1)` first to `H=F` and then to `H=Gamma`.  The order of
`[omega]` divides both indices, hence their greatest common divisor.  If that
gcd is one, Bezout gives `[omega]=0`.
