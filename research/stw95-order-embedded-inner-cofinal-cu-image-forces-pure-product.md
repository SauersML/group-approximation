---
rg: 2
id: stw95-order-embedded-inner-cofinal-cu-image-forces-pure-product
kind: claim
title: Order reflection turns inner cofinality of a Cu image into an isomorphism
distinct_from:
  split-cu-tensor-map-implies-pure-product: that assumes a right inverse and concludes purity without injectivity; this theorem identifies the exact effect of adding order reflection to local inner cofinality, namely that the canonical map is already a Cu-isomorphism.
  stw95-inner-cofinal-cu-image-gives-almost-divisibility: that uses the same local cofinality to transfer only almost divisibility; this adds order reflection and proves almost unperforation as well.
  stw95-ordered-retract-gives-almost-unperforation: that pulls arbitrary concrete elements back through a global ordered-monoid retraction; this localizes each comparison to elements already in the external image and needs no map out of the concrete semigroup.
---

Let `S,T` be Cu-semigroups and let `theta:S->T` be a Cu-morphism.  Suppose
that `theta` is an order embedding and that its image is inner cofinal for
way-below pairs: whenever `x'<<x` in `T`, there are `a'<<a` in `S` such that

```text
x'<=theta(a'),              theta(a)<=x.              (IC)
```

Then `theta` is a Cu-isomorphism.  Conversely, every Cu-isomorphism satisfies
`(IC)`.  Thus, in the presence of order reflection, inner cofinality is
equivalent to surjectivity and is not a genuinely weaker substitute for it.

In particular, if `A` and `B` are pure C-star algebras and

```text
S=Cu(A) tensor_Cu Cu(B),       T=Cu(A tensor_min B),
```

and the canonical external map has the two displayed properties, then it is
an isomorphism and `A tensor_min B` is pure.  The useful strictly weaker
one-axiom result remains
`stw95-inner-cofinal-cu-image-gives-almost-divisibility`, where order
reflection is not assumed.
