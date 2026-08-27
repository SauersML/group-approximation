---
rg: 2
id: residually-finite-conjugacy-difference-coloring-proof
kind: route
title: Separate all prototype differences in one finite quotient
target: rf-conjugacy-difference-graphs-finitely-colorable
requires: []
---

For each `w_i`, residual finiteness gives a finite quotient
`q_i:H->Q_i` with `q_i(w_i)!=1`.  The diagonal product

```text
q:H->Q_1 x ... x Q_r
```

has finite target and separates every `w_i`.  Color `x in H` by `q(x)`.

If adjacent `x,y` had the same color, then `q(x^(-1)y)=1`.  But adjacency
gives

```text
x^(-1)y=h w_i^(+1 or -1) h^(-1)
```

for some `h`, whose image is a conjugate of the nonidentity element
`q(w_i)^(+1 or -1)`.  This contradiction proves the coloring is proper.
