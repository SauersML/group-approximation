---
rg: 2
id: intrinsic-compression-defect-functoriality-and-saturation-proof
kind: route
title: Transport defect generators and close their simple normal images
target: intrinsic-compression-defect-functoriality-and-saturation
requires:
  - compression-defect-dies-in-finite-dimensions
  - normal-kazhdan-defect-non-mf
---

Let

```text
x=[ucu^-1,l]                                               (ICP1)
```

be a defining generator of `D_G(L)`.  For a homomorphism `f:G->Q`,

```text
f(u) f(L) f(u)^-1 <= f(L),
f(c) in C_(f(G))(f(L)),
f(x)=[f(u)f(c)f(u)^-1,f(l)].                              (ICP2)
```

Thus `f(x)` is a defining generator of `D_(f(G))(f(L))`.  Normal closure
gives `(ICD2)`.

For products, compressor and centralizer conditions are coordinatewise, so
every defining generator for the left side of `(ICD3)` belongs to the right
side.  Conversely, choose the identity for `c,l` in the second coordinate
to realize every first-coordinate generator as `(x,1)`, and interchange the
coordinates to realize `(1,y)`.  Their normal closures generate the full
direct product, proving `(ICD3)`.

`compression-defect-dies-in-finite-dimensions` proves item 3 for precisely
the generators `(ICP1)` and hence for their normal closure.

Put `D=D_G(L)`.  Since `D` is normal in `G`, the intersection `D intersect S`
is normal in `S`.  If it is nontrivial and `S` is simple, it is all of `S`.
If `S` normally generates `G`, normality of `D` then gives `D=G`.  This is
item 4.

For item 5, functoriality gives

```text
f(S)<=f(D_G(L))<=D_Q(f(L)).                               (ICP3)
```

The last group is normal in `Q`, so it contains the normal closure of
`f(S)`, which is `Q`.  This proves `(ICD4)`.  Finally,
`normal-kazhdan-defect-non-mf` applied with the normal Kazhdan subgroup
`K=Q` gives `(ICD5)`.
