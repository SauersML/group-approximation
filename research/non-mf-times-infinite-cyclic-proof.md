---
rg: 2
id: non-mf-times-infinite-cyclic-proof
kind: route
title: Restrict an MF embedding to the seed and use characters of the cyclic quotient
target: non-mf-times-infinite-cyclic-is-non-mf-and-nonkazhdan
requires: []
---

If `B x Z` embedded in a norm matrix corona, restriction to
`B x {0}` would embed `B`; subgroup heredity therefore proves non-MF.

For failure of property `(T)`, let `Q subset B x Z` be finite and
`epsilon>0`.  If `M` bounds the absolute values of the cyclic coordinates in
`Q`, choose `t` nonzero modulo `2*pi` and sufficiently small that

```text
|exp(i t n)-1|<epsilon                 for |n|<=M.
```

The one-dimensional character `(b,n) |-> exp(i t n)` has a
`(Q,epsilon)`-almost invariant unit vector and no nonzero invariant vector.
Thus no Kazhdan pair exists.

If `B=<S|R>`, then

```text
B x Z=<S,t | R, [t,s]=1 for s in S>,
```

which proves the finite-generation and finite-presentation assertions.

