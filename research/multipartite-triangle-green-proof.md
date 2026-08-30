---
rg: 2
id: multipartite-triangle-green-proof
kind: route
title: Invert the divergence-free multipartite curl block
target: multipartite-triangle-curl-has-uniform-infinity-green-bound
requires: []
---

Orient every edge and triangle once and use unnormalized counting inner
products.  The multipartite clique complex has `H^1=0`, so the
Moore--Penrose representative is divergence free.  Summing its triangle
curls over the `(r-2)m` third vertices gives `(MTG6)` and the coarse estimate
for `r>=5`.

For an `m by m` edge block, let `R,L` be the commuting row- and column-mean
projections.  On the divergence-free space,

```text
delta_1^*delta_1=qI+m(R+L),       q=(r-2)m.
```

The stated coefficients `a,b,c` invert this operator in
`aI+b(R+L)+cRL`.  The divergence-free space is invariant, while
`delta_1^*` lands in it, so this inverse composed with `delta_1^*` is the
Moore--Penrose Green operator.  Counting the three triangle classes in one
row gives `(MTG10)` and the exact absolute row sum `B_(r,m)`.  Writing
`x=(m-2)/m` makes it a convex quadratic on `[-1,1)`, whose endpoint bound is
`1+2(r+1)/(r(r-1))<=7/3`.
