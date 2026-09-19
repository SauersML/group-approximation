---
rg: 2
id: stw99-xcix-nuclear-radius-proof
kind: route
title: Apply the quantitative nuclear perturbation isomorphism theorem
target: stw99-xcix-nuclear-radius-positive
requires: []
---

Choose `gamma` with

```text
d(A,B) < gamma < 1/420000.
```

Christensen--Sinclair--Smith--White--Winter, Theorem 4.3 in
[Perturbations of nuclear C*-algebras](https://arxiv.org/abs/0910.4953),
gives a surjective *-isomorphism `A -> B` because `A` is separable and
nuclear.  Tensorial absorption of Z is invariant under *-isomorphism:

```text
B tensor Z  ~=  A tensor Z  ~=  A  ~=  B.
```

Thus `B` is Z-stable.  The theorem's stronger finite-set estimate
`28 sqrt(gamma)` is not needed here.
