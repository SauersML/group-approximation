---
rg: 2
id: stw83-finite-kirchberg-core-circle-quotient-dimension-one-proof
kind: route
title: Combine the finite graph decomposition with two-color Kirchberg-by-circle extension reuse
target: stw83-finite-kirchberg-core-circle-quotient-dimension-one
requires: []
---

Evington--Ng--Sims--White, Proposition 5.1 in
[Nuclear dimension of extensions of commutative C*-algebras by Kirchberg algebras](https://arxiv.org/abs/2409.12872),
shows that the five graph conditions are equivalent to an exact sequence

```text
0 -> J -> C*(F) -> A -> 0
```

in which `J` is an essential stable Kirchberg ideal and `A` is stably isomorphic
to `C(X)`, where `X` is a nonempty finite disjoint union of circles.  Their
Corollary 4.2 proves

```text
dim_nuc(C*(F)) = max(1,dim(X)) = 1.
```

Essentiality and the direction of the extension matter: the theorem has a
Kirchberg ideal and a stably commutative quotient, not the reverse.
