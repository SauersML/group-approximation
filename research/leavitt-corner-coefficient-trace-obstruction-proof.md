---
rg: 2
id: leavitt-corner-coefficient-trace-obstruction-proof
kind: route
title: Compare the identity coefficients of the order-three and primitive packet idempotents
target: group-algebra-coefficient-trace-separates-leavitt-corners
requires:
  - leavitt-primitive-corner-recursive-extension
---

The prerequisite places `u,v,g=uv` in one constant subgroup
`H congruent S_3`, with `u,v` distinct transpositions and `g` of order three.
Therefore the identity coefficients of

```text
e=[g]+[g^2],             f=[1]+[u]+[v]+[g]
```

are respectively zero and one.  Coefficient of the identity is cyclic on
every group algebra: the coefficient in `ab` is
`sum_r a_r b_(r^(-1))`, unchanged after swapping `a,b` and replacing `r` by
`r^(-1)`.  An equivalence `xy=e`, `yx=f` would force these unequal
coefficients to agree, which is impossible in `F_2`.
