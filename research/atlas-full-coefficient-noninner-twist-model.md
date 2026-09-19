---
rg: 2
id: atlas-full-coefficient-noninner-twist-model
kind: route
title: Use a noninner automorphism of the growing Atlas coefficient block
target: binary-leavitt-unit-group-hyperlinear
requires:
  - leavitt-atlas-full-coefficient-purification
---

Starting from a purified relative unitary

```text
U in U(l2(A8) tensor C^r),       C*(U_xy)=M_r(C),
```

apply a multiplicative star-preserving automorphism of the full coefficient
algebra simultaneously to every block `U_xy`.  The proposed extra degree of
freedom was a growing "outer" or semilinear coefficient twist, intended to
leave the one-parameter commutative band walls while preserving unitarity and
the two exact regular `A8` margins.

This route is invalidated by
`atlas-full-coefficient-automorphism-twists-are-gauge`.  Every complex-linear
star automorphism of `M_r(C)` is unitarily inner, so simultaneous blockwise
application is exactly a left/right regular-chart commutant gauge and changes
no Atlas word defect.  Allowing a real-linear star automorphism adds only the
entrywise-conjugate certificate, which has the same defects because the
regular `A8` matrices and the literal words are real.

Position-dependent transformations of different blocks are outside this
no-go, but they are not one coefficient-algebra automorphism: they must prove
block unitarity and all mixed multiplicative constraints anew.  Likewise the
genuine outer automorphism of the `A8` label group is not a coefficient twist
and is not excluded here.
