---
rg: 2
id: literal-base-explicit-kazhdan-pair-proof
kind: route
title: Push the sharp P13 spectral gap through the short words and affine bridge
target: literal-base-explicit-kazhdan-pair
requires: []
artifacts:
  - GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean
  - GroupApproximation/Monsters/P13SpectralGap.lean
  - GroupApproximation/Sofic/LiteralBaseP13RotationQuotient.lean
  - GroupApproximation/Monsters/P13CircumcenterRouteStep3.lean
  - GroupApproximation/Sofic/LiteralBasePropertyTBridge.lean
---

## Direct proof

For the six-generator P13 Laplacian `Delta`,
`P13SpectralGap.t1_04_p13_spectrum_subset` proves

```text
spectrum(Delta) subset {0} union [1/500,infinity),
```

and `t1_05_p13_ker_eq_invariants` identifies `ker Delta` with the invariant
vectors. In a representation without nonzero invariant vectors, the isolated
spectral point `0` is absent: an isolated spectral point of a bounded
self-adjoint operator has nonzero spectral projection and hence is an
eigenvalue. Thus `spectrum(Delta) subset [1/500,infinity)`, and the spectral
theorem gives

```text
sum_(i=1)^6 ||rho(e_i)x-x||^2
  = <x,Delta x> >= (1/500)||x||^2.
```

For a unit vector, if every generator displacement were strictly less than
`1/sqrt(3000)`, their six squared displacements would sum to strictly less
than `6/3000=1/500`, a contradiction. Hence the six P13 generators with
`kappa13=1/sqrt(3000)` form a Kazhdan pair.

A Kazhdan pair pushes through a surjective homomorphism without tolerance
loss. Apply this first to
`LiteralBaseP13RotationQuotient.p13ToRotation_surjective`, then to
`P13CircumcenterRouteStep3.rotationToRotations_surjective`. The public word
lemmas `p13ToRotation_E12_word` through `p13ToRotation_E32_word` identify
the resulting six controls with the words in the claim. Also
`0<kappa13<=1`.

Now repeat `LiteralBasePropertyTBridge.exists_global_fixed_near`. If a unit
vector `x` is moved by less than `kappa13/64` on those six words and on
`v2,v3`, its rotation-moving projection has norm less than `1/64`. Writing
`p` for its rotation-fixed projection gives `||p-x||<1/64`. The exact affine
relations make the three basis translations move `p` by less than `3/64`;
the checked two-conjugate normal form makes every translation move `p` by at
most `1/8`. The translation-orbit circumcenter and the normalizer projection
then give a globally fixed `y` with

```text
||y-x||<1/8+1/64<1.
```

Since `||x||=1`, `y` is nonzero. This proves the affine pair with
`kappaB=kappa13/64`.

Finally `S_B` has at most `17` elements. The standard Kazhdan orbit-average
estimate gives contraction
`1-kappaB^2/(4|S_B|) <= 1-kappaB^2/68`, and
`kappaB^2/68=1/(64^2*3000*68)=1/835584000`.

The fallback constant in the claim follows by instead unfolding
`ExactHodgeCertificate.certifiedKazhdanTolerance` at `c=1/250`, `r=1/500`,
and six generators, then applying the same two quotient maps and the same
`/64` affine bridge.
