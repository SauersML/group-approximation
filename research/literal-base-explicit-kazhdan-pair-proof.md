---
rg: 2
id: literal-base-explicit-kazhdan-pair-proof
kind: route
title: Push the rational P13 pair through the short words and the affine bridge
target: literal-base-explicit-kazhdan-pair
requires: []
artifacts:
  - GroupApproximation/Kazhdan/ExactHodgeCertificate.lean
  - GroupApproximation/Monsters/P13SpectralGap.lean
  - GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean
  - GroupApproximation/Sofic/LiteralBaseP13RotationQuotient.lean
  - GroupApproximation/Monsters/P13CircumcenterRouteStep3.lean
  - GroupApproximation/Sofic/LiteralBasePropertyTBridge.lean
---

## Direct proof

`P13SpectralGap.t1_04_p13_spectrum_subset` places the spectrum of the
six-generator Laplacian in `{0} union [1/500,infinity)`, and
`P13SpectralGap.t1_05_p13_ker_eq_invariants` identifies its kernel with the
invariant subspace. By the spectral theorem, on the orthogonal complement of
the invariant subspace,

```text
sum_(i=1)^6 ||rho(e_i)x-x||^2 >= (1/500)||x||^2.
```

Thus if all six generator displacements are strictly less than
`1/sqrt(3000)` for a unit vector, its moving projection has norm strictly
less than one and its invariant projection is nonzero. Hence the six P13
generators have Kazhdan tolerance

```text
kappa13=1/sqrt(3000).
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
`kappa13/64=kappaB=1/(64*sqrt(3000))`.

Finally enlarge `Q_B` to the symmetric identity-containing `S_B`. It has at
most `2*8+1=17` elements. `IsKazhdanPair.norm_orbitAverage_le` gives moving
contraction `1-kappaB^2/(4*|S_B|)`, which is at most
`1-kappaB^2/68=1-1/835584000`.
