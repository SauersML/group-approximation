---
rg: 2
id: rank-four-jacobson-head-retention-proof
kind: route
title: Use the simple self-centralizing finitary kernel in rank four
target: rank-four-jacobson-head-retention-is-faithful
requires: []
---

Put `Q=1-xy`. The elements

```text
E_mn=x^m Q y^n
```

are the ordinary finite matrix units on the one-sided basis. Elementary
roots with coefficients `E_mn` give transvections between distinct
coordinate rays; commutators through a third matrix coordinate give
transvections within one ray. Since the matrix rank is four, this produces

```text
L=GL_fin(N x {1,2,3,4},F_2)
```

as a normal subgroup of `Gamma`. The usual fresh-coordinate commutator
argument proves that `L` is infinite simple.

An operator on the direct-sum module commuting with every finitary
transvection preserves every coordinate line and has the same scalar on
every line. Over `F_2` the only invertible scalar is `1`. Hence `(RJH1)`.

Let `K=ker(phi)`. If `phi(c)!=1` for `1!=c in L`, simplicity gives

```text
K intersect L=1.
```

For `k in K`, normality of `L` gives

```text
[k,L] <= K intersect L=1.
```

Thus `k in C_Gamma(L)=1`, proving `(RJH2)`.
