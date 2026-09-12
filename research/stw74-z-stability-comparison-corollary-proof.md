---
rg: 2
id: stw74-z-stability-comparison-corollary-proof
kind: route
title: Import almost unperforation from Z and exclude the elementary finite-dimensional case
target: stw74-z-stability-and-finite-nuclear-dimension-close-hinge
requires:
  - stw74-unit-almost-unperforation-closes-hinge
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

Rordam's Theorem 4.5 in
[*The stable and the real rank of Z-absorbing C*-algebras*](https://arxiv.org/abs/math/0408020)
says that a Z-stable C*-algebra has almost unperforated Cuntz semigroup.
Applying the theorem to `A tensor K` gives the standard completed formulation

```text
Cu(A) is almost unperforated.
```

This is exactly the sufficient hypothesis already isolated in
`stw74-unit-almost-unperforation-closes-hinge`.  That theorem therefore makes
`A` purely infinite.  No part of its finite-unit-root or property-(SP) proof
is repeated here.

Now suppose that `A` is also separable and has finite nuclear dimension.  A
simple unital elementary C*-algebra is a matrix algebra.  Its rank-one
projections are finite, so no elementary algebra can satisfy the LXXIV
projection hypothesis.  Thus `A` is non-elementary.  Winter's finite nuclear
dimension theorem
([*Nuclear dimension and Z-stability of pure C*-algebras*](https://arxiv.org/abs/1006.2731))
then gives

```text
finite nuclear dimension => Z-stability
```

for this separable simple unital non-elementary algebra.  The first paragraph
applies and proves pure infiniteness.

Taking contrapositives gives the obstruction statements.  Any LXXIV
counterexample is non-Z-stable; if it is separable, finite nuclear dimension
would force Z-stability and is therefore impossible, so its nuclear dimension
is infinite.
