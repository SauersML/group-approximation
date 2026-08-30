---
rg: 2
id: literal-base-explicit-kazhdan-pair-proof
kind: route
title: Push the rational P13 pair through the short words and the affine bridge
target: literal-base-explicit-kazhdan-pair
requires: []
artifacts:
  - GroupApproximation/Kazhdan/ExactHodgeCertificate.lean
  - GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean
  - GroupApproximation/Sofic/LiteralBaseP13RotationQuotient.lean
  - GroupApproximation/Monsters/P13CircumcenterRouteStep3.lean
  - GroupApproximation/Sofic/LiteralBasePropertyTBridge.lean
---

## Direct proof

`LiteralP13HodgeCertificate.cleanP13Certificate` has certificate constants
`c=1/250`, `r=1/500`, and six generators. Thus the `gamma` in
`ExactHodgeCertificate.certifiedKazhdanTolerance` is `1/500`, while its
universal upper bound is

```text
max(1/500,4*6)=24.
```

`Certificate.isKazhdanPair` therefore gives the six P13 generators the exact
tolerance

```text
(1/500)*(1-sqrt(1-(1/500)/24))/(2*6)
  =(1-sqrt(11999/12000))/6000
  =kappa13.
```

A Kazhdan pair pushes through a surjective homomorphism with no loss of
tolerance: compose an orthogonal representation of the quotient with the
surjection, apply the original pair, and use surjectivity to turn invariance
under the source into invariance under the quotient.
`LiteralBaseP13RotationQuotient.p13ToRotation_surjective` and
`P13CircumcenterRouteStep3.rotationToRotations_surjective` therefore give the
rotation subgroup the same tolerance on the images of the six generators.
The public word lemmas `p13ToRotation_E12_word` through
`p13ToRotation_E32_word` identify those images with exactly the six displayed
words. Also `0<kappa13<=1`.

It remains to repeat the quantitative argument already proved inside
`LiteralBasePropertyTBridge.exists_global_fixed_near`. Let `rho` be an
honest orthogonal representation of `B`, let `||x||=1`, and suppose every
element of `Q_B` moves `x` by less than `kappa13/64`. The Kazhdan
estimate on the rotation moving subspace makes the moving projection of `x`
have norm less than `1/64`. If `p` is the rotation-fixed projection, then

```text
||p-x||<1/64.
```

The two controlled translations `v2,v3` move `p` by less than `3/64`; the
printed conjugacy for `v1` gives the same basis-translation estimate. The
checked two-conjugate translation normal form then gives

```text
||rho(a)p-p||<=1/8
```

for every translation `a`. The circumcenter theorem supplies a
translation-fixed point within `1/8` of `p`. Projecting onto the
translation-fixed subspace preserves rotation invariance because rotations
normalize translations, so one obtains a vector `y` fixed by all of `B` and

```text
||y-x|| <= ||y-p||+||p-x|| < 1/8+1/64 < 1.
```

Hence `y` is nonzero. This is the Kazhdan-pair assertion with tolerance
`kappa13/64=kappaB`.

Finally enlarge `Q_B` to the symmetric identity-containing `S_B`. It has at
most `2*8+1=17` elements. `IsKazhdanPair.norm_orbitAverage_le` gives moving
contraction `1-kappaB^2/(4*|S_B|)`, which is at most
`1-kappaB^2/68`.
