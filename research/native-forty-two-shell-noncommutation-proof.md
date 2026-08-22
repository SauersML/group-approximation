---
rg: 2
id: native-forty-two-shell-noncommutation-proof
kind: route
title: Compare dyadic elementary divisors and use the exact graph-product model
target: native-forty-two-shell-has-a-noncommuting-pair
requires:
  - native-sl3-group-is-hecke-graph-wreath-product
  - native-sl3-edge-parahoric-has-index-forty-two
---

Choose a determinant-one signed permutation matrix `w_0 in C` reversing the
first and third basis vectors.  Then `w_0 h w_0^(-1)=h^(-1)`, so both
displayed labels belong to `ChC/C`.

Adjacency of `hC` and `h^(-1)C` would say

```text
h^(-1)h^(-1) in C h C.
```

Left and right multiplication by `SL_3(Z_2)` preserve the elementary
divisors of a rational 2-adic matrix.  Those of `h^(-2)` have valuations
`(-2,0,2)`, while those of `h` have valuations `(-1,0,1)`, proving
nonadjacency.

The graph-product normal form then says the two vertex involutions have no
commutation relation and their alternating products are reduced.  In the
canonical group trace, `c_xc_y` and `c_yc_x` are distinct group elements,
so the squared 2-norm of their difference is `1+1=2`.  Scaling by `1/4`
gives `(N42A3)`.  Finally `h^2C` has the excluded double-coset profile, which
proves failure of fixed-shell normalization.
