---
rg: 2
id: thompson-r5-a6-seam-to-carmichael-family
kind: route
title: Globalize pointwise R5 seam control into the uniform Thompson Carmichael family
target: thompson-v-r5-coherent-carmichael-family
requires:
  - thompson-v-r5-a6-seam-pointwise-synchronization
  - pointwise-a5-overlap-globalizes-carmichael-family
---

Apply the abstract globalization theorem to the contextual matrices supplied
by the R5 seam claim, with

```text
eta=C delta,                 epsilon=C delta.
```

It produces literal conjugates `X_i` of the single matrix `B=U(b)` satisfying

```text
||X_i^3-I||_2 <= C delta,
||(X_iX_j)^2-I||_2 <= 9 C delta                 (i!=j),
```

uniformly in the matrix dimension and in `M`.  After replacing `C` by `9C`,
these are exactly the conditions in
`thompson-v-r5-coherent-carmichael-family`.  The existing compact-packing
route then gives linear collapse of `U(b)`, the strict Thompson word ceiling,
and hence a nonhyperlinear group.

