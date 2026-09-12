---
rg: 2
id: cdi-native-envelope-inclusion-is-infinite-index
kind: claim
title: The native CDI embedding has infinite Jones index
distinct_from:
  cdi-property-t-envelope-has-nonabelian-base: that claim identifies the tensor-base/cocycle-crossed-product structure and rules out a compact-abelian envelope; the present claim computes the index of the embedded input coordinate and rules out reading the construction as a finite-index or finite-fixed-point promotion.
---

In the Chifan--Drimbe--Ioana construction, write

```text
Q = M^B crossed_product_(beta,w) B
```

as in their Proposition 3.8, where `B` is infinite, and embed the input factor
`M` as the identity coordinate `M^e` of `M^B`.  Then

```text
[Q:M^e] = infinity.
```

Indeed, the relative commutant `(M^e)' intersect Q` contains the diffuse
factor `M^(B\{e})`.  A finite-index inclusion of finite factors has
finite-dimensional relative commutant.  Consequently the native CDI
envelope cannot be reinterpreted as a matrix amplification, a finite-group
fixed-point overfactor, or any other finite-index promotion of the non-CE
input.

