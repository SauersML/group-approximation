---
rg: 2
id: rank-four-jacobson-head-retention-is-faithful
kind: claim
title: Retaining any rank-four Jacobson head element is projectively faithful
artifacts:
  - research/rank-four-jacobson-head-retention-proof.md
distinct_from:
  binary-jacobson-head-retaining-homomorphisms-are-faithful: that treats EL_5 and one specified head transvection; this treats EL_4 and every nontrivial element of the finitary kernel, as required by the Toeplitz parity compressor.
---

**ESTABLISHED.** Let

```text
T=F_2<x,y | yx=1>,             Gamma=EL_4(T),
L=GL_fin(N x {1,2,3,4},F_2).
```

Under the standard one-sided shift representation, `L` is an infinite
simple normal subgroup of `Gamma` and

```text
C_Gamma(L)=1.                                             (RJH1)
```

Consequently, for every group `D`, every homomorphism
`phi:Gamma->D`, and every `1!=c in L`,

```text
phi(c)!=1  ==>  phi is injective.                         (RJH2)
```

In particular this applies when `D` is a projective unitary group.

DERIVATION
rank-four-jacobson-head-retention-proof
