---
rg: 2
id: steinberg-block-bezout-equivalence-proof
kind: route
title: Left-invert the stacked Fox rows inside the Steinberg matrix block
target: steinberg-fox-injectivity-is-block-bezout
requires:
  - steinberg-fox-kernel-is-flag-incidence
---

The defining-characteristic Steinberg module is absolutely irreducible.
Hence its group-algebra image is the full matrix algebra, giving the first
identity in `(SBB1)`.  Put

```text
T:St_p -> St_p direct_sum St_p,       T(v)=(xv,yv).
```

The common kernel is zero exactly when `T` is injective.  Over a field, an
injective map between finite-dimensional spaces has a left inverse
`L:St_p direct_sum St_p -> St_p`.  Write `L(v,w)=av+bw`; fullness of `A_p`
puts `a,b` in `A_p`.  The equality `LT=1` is precisely

```text
a x + b y = 1.
```

Conversely this identity sends every common-kernel vector to itself and
therefore forces it to vanish.  Finally `(SFI4)` identifies this common
kernel with `ker D_p`, proving every equivalence in `(SBB1)`.
