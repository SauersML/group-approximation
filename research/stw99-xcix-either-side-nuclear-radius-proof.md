---
rg: 2
id: stw99-xcix-either-side-nuclear-radius-proof
kind: route
title: Use symmetry of Kadison--Kastler distance before applying the nuclear isomorphism theorem
target: stw99-xcix-either-side-nuclear-radius
requires: []
---

Choose `gamma` with

```text
d(A,B) < gamma < 1/420000.
```

If `A` is separable and nuclear, Christensen--Sinclair--Smith--White--Winter,
Theorem 4.3 in
[Perturbations of nuclear C*-algebras](https://arxiv.org/abs/0910.4953),
applied to `(A,B)`, gives a surjective *-isomorphism `A -> B`.

If instead `B` is separable and nuclear, use the symmetry
`d(B,A)=d(A,B)` and apply the same theorem to the ordered pair `(B,A)`.
This gives a surjective *-isomorphism `B -> A`.  In either case `A` and `B`
are *-isomorphic.  Tensorial absorption is invariant under *-isomorphism, so

```text
B tensor Z  ~=  A tensor Z  ~=  A  ~=  B.
```

Thus `B` is Z-stable.  Notice that the reversed application genuinely uses
separability of `B`; no claim is made for a nuclear but nonseparable target.
