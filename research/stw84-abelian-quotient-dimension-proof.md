---
rg: 2
id: stw84-abelian-quotient-dimension-proof
kind: route
title: Pass to the Pontryagin dual of the abelianization
target: stw84-abelianization-rank-lower-bound
requires: []
---

The quotient homomorphism `G -> G_ab` induces a surjective *-homomorphism

```text
C*(G) -> C*(G_ab).
```

Nuclear dimension does not increase on quotients.  For a countable discrete
abelian group `A`, Fourier transform identifies

```text
C*(A)=C(A_hat).
```

The nuclear dimension of a separable commutative C*-algebra is the covering
dimension of its spectrum.  Pontryagin dimension theory gives

```text
dim(A_hat)=rank(A)=dim_Q(Q tensor_Z A),
```

with both sides infinite simultaneously.  Applying this to `A=G_ab` yields

```text
dim_nuc(C*(G)) >= dim_nuc(C*(G_ab))=r(G).
```

The compact-group dimension formula is proved directly in Sidney Morris,
[*Pontryagin Duality and the Structure of Locally Compact Abelian
Groups*](https://sidneymorris.net/Pontryagin_Duality.pdf), Theorem 30 and its
fourth corollary.  No finite-generation hypothesis is present.

