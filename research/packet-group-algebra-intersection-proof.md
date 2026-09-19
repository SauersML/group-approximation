---
rg: 2
id: packet-group-algebra-intersection-proof
kind: route
title: Compare coefficients in the canonical group basis
target: common-carrier-lives-in-packet-intersection
requires: []
---

Every element `a` of `K[Gamma]` has one unique finite expansion

```text
a=sum_(g in Gamma) a_g g.                              (CPIP1)
```

Membership in `K[H_i]` is equivalent to `a_g=0` for every `g` outside
`H_i`.  Hence membership in every `K[H_i]` is equivalent to

```text
supp(a) subset intersection_i H_i,                    (CPIP2)
```

which is precisely membership in the right side of `(CPI1)`.  Apply this
to `(CPI2)`.  Each `H_c` is finite, so their intersection `K_x` is finite,
and `(CPI3)` follows.
