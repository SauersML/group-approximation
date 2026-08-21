---
rg: 2
id: finite-index-double-misses-iwahori-proof
kind: route
title: Detect the nonextendable Iwahori edge twist in modular abelianization
target: finite-index-double-theorem-misses-iwahori-twist
requires: []
---

Conjugation by `d=diag(sqrt(2),1/sqrt(2))` scales an upper-unipotent
parameter by `2` and a lower-unipotent parameter by `1/2`.  Hence

```text
d u d^(-1)=u^2,        d ell^2 d^(-1)=ell.
```

If this edge isomorphism extended to `alpha in Aut(PSL_2(Z))`, its induced
map on the abelianization would take `[u]` to `2[u]`.  From
`PSL_2(Z)=C_2*C_3`, its abelianization is `C_2 x C_3=C_6`; the standard
parabolic `u` maps to a generator (equivalently, writing
`u` as the product of the standard order-two and order-three generators
gives class `(1,1)`).  Its double has order three.  This contradicts
invertibility of the induced map on abelianization.

Gao--Kunnawalkam Elayavalli--Mj assume that every edge inclusion is the same
fixed inclusion `H<G`; Corollary 1.3 treats the corresponding identity
double.  Since the Iwahori twist cannot be absorbed into a vertex
automorphism, their hypothesis is not satisfied.
