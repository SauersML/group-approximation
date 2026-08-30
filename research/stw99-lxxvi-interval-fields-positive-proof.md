---
rg: 2
id: stw99-lxxvi-interval-fields-positive-proof
kind: route
title: Apply the natural lower-semicontinuous-function formula fiberwise
target: stw99-lxxvi-interval-fields-over-simple-pure-fibers
requires: []
---

By Lin's stable-rank theorem quoted as STW Theorem 21, the simple separable
stably finite pure algebra `D` has stable rank one.  The tensor product
`D tensor Z` is simple, stably finite, Z-stable, and also has stable rank one.

Antoine--Dadarlat--Perera--Santiago, Theorem 2.6 in
[Recovering the Elliott invariant from the Cuntz semigroup](https://arxiv.org/abs/1109.5803),
gives natural order isomorphisms

```text
Cu(C([0,1],D))            ~= Lsc([0,1],Cu(D)),
Cu(C([0,1],D tensor Z))   ~= Lsc([0,1],Cu(D tensor Z)),
```

by evaluating a positive field at each point.  STW Proposition 23 says that
the first-factor map `Cu(D)->Cu(D tensor Z)` is an isomorphism because `D` is
simple, separable, stably finite, and pure.  Applying this isomorphism
pointwise gives an isomorphism between the two lower-semicontinuous-function
semigroups.  Naturality of evaluation makes the resulting square commute, so
the left vertical map is exactly the first-factor Cu map for the interval
field and is an isomorphism.

