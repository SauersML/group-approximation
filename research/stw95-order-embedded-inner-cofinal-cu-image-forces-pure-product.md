---
rg: 2
id: stw95-order-embedded-inner-cofinal-cu-image-forces-pure-product
kind: claim
title: Order reflection plus inner cofinality of the external Cu image forces tensor purity
distinct_from:
  split-cu-tensor-map-implies-pure-product: that assumes a Cu-morphism right inverse, which makes the external map surjective; this permits a genuinely nonsurjective external map and instead assumes order reflection plus local inner cofinality.
  stw95-inner-cofinal-cu-image-gives-almost-divisibility: that uses the same local cofinality to transfer only almost divisibility; this adds order reflection and proves almost unperforation as well.
  stw95-ordered-retract-gives-almost-unperforation: that pulls arbitrary concrete elements back through a global ordered-monoid retraction; this localizes each comparison to elements already in the external image and needs no map out of the concrete semigroup.
---

Let `A` and `B` be pure C\*-algebras, set

```text
S=Cu(A) tensor_Cu Cu(B),
T=Cu(A tensor_min B),
```

and let `theta:S->T` be the canonical external-product Cu-morphism.  Assume:

1. `theta` is an order embedding; that is,

```text
theta(s)<=theta(t)  implies  s<=t;
```

2. its image is inner cofinal for way-below pairs: whenever `x'<<x` in
   `T`, there are `a'<<a` in `S` such that

```text
x'<=theta(a'),              theta(a)<=x.              (IC)
```

Then `A tensor_min B` is pure.

In particular, surjectivity of the external Cu map is not required.  Every
concrete element may lie outside its image, provided each way-below window
can be bracketed as in `(IC)`.
