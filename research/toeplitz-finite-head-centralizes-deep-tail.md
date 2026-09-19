---
rg: 2
id: toeplitz-finite-head-centralizes-deep-tail
kind: claim
title: Every finite Toeplitz head is a full matrix algebra centralizing the deep recursive tail
distinct_from:
  toeplitz-tail-plus-one-swap-generates: that shows one head transposition and the first tail generate the whole ring; this computes every finite head algebra and its exact commutation with the corresponding deep tail.
  truncated-polynomial-binary-weyl-expander-tower: that supplies finite Weyl levels and quantum expansion; this supplies an actual recursive coefficient-ring head-tail factorization.
---

In `T=F_2<x,y | yx=1>`, put

```text
f_i=x^i(1+xy)y^i,                e_(ij)=x^i(1+xy)y^j.
```

For every `N>=1`,

```text
F_N=span_(F_2){e_(ij):0<=i,j<N} ~= M_N(F_2),                  (TFH1)
```

and `F_N` commutes with `sigma^N(T)`. More precisely,

```text
sigma^N(a)=x^N a y^N+eps(a) sum_(i=0)^(N-1) f_i,              (TFH2)
```

so for every `c in F_N`,

```text
c sigma^N(a)=sigma^N(a)c=eps(a)c.                             (TFH3)
```

The adjacent swaps `sigma^i(s)` from
`toeplitz-tail-plus-one-swap-generates` act as the standard transpositions of
head coordinates `i,i+1`. Hence every fixed finite matrix packet can be
placed in a bounded Toeplitz head, while the entire depth-`N` recursive tail
acts only on its external multiplicity space.

This is the exact algebraic tensor interface needed for residual Schur
recursion. It does not supply a lower bound for the tail commutant density in
finite-dimensional group microstates.

