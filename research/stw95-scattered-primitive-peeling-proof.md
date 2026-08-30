---
rg: 2
id: stw95-scattered-primitive-peeling-proof
kind: route
title: Peel isolated primitive points and apply the nuclear-layer tensor theorem
target: stw95-scattered-primitive-local-product-test
requires:
  - stw95-nuclear-successor-filtrations-need-no-exact-factor
  - stw95-nonunital-ash-factor-preserves-purity
artifacts:
  - research/artifacts/stw95-scattered-primitive-tensor-localization-audit-2026-08-30.md
---

Put `X=Prim(B)`.  Recursively construct open subsets `U_alpha` of `X`.
Start with `U_0=emptyset`.  If `U_alpha!=X`, scatteredness of the subspace
`X\U_alpha` gives an isolated point `x_alpha`.  Thus there is an open set
`O_alpha` in `X` such that

```text
O_alpha intersect (X\U_alpha)={x_alpha}.
```

Set

```text
U_(alpha+1)=U_alpha union {x_alpha}=U_alpha union O_alpha,
```

which is open.  At a limit ordinal take the union of the preceding open
sets.  The recursion removes one new point at every successor and therefore
reaches `X` at some ordinal `gamma`.

Let `J_alpha` be the ideal of `B` corresponding to `U_alpha`.  The
ideal--open-set correspondence and continuity at limit ordinals give

```text
J_0=0,                     J_gamma=B,
J_lambda=closure(union_(alpha<lambda) J_alpha),
Prim(J_(alpha+1)/J_alpha)={x_alpha}.                  (SPP1)
```

A C*-algebra with singleton primitive spectrum is simple.  Indeed, the
intersection of its primitive ideals is zero, while every proper nonzero
ideal is contained in a primitive ideal obtained from an irreducible
representation of the corresponding quotient.  Hence every successor
layer in `(SPP1)` is a nonzero simple subquotient of `B`.

Under `(SPT1)`, these layers are nuclear and their minimal tensor products
with `A` are pure.  The filtration `(J_alpha)` is exactly the input required
by `stw95-nuclear-successor-filtrations-need-no-exact-factor`; separability
of `B` handles its limit stages.  That theorem yields purity of
`A tensor_min B`, proving `(SPT2)`.

For the ASH corollary, every simple layer is separable because it is a
subquotient of the separable algebra `B`.  If `A` is pure and is either
simple or residually stably finite, then
`stw95-nonunital-ash-factor-preserves-purity` makes `A tensor_min L` pure
for every such ASH layer `L`.  ASH algebras are nuclear, so `(SPT1)` holds
and the general result applies.
