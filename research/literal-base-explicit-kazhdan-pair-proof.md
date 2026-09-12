---
rg: 2
id: literal-base-explicit-kazhdan-pair-proof
kind: route
title: Optimize the sharp P13 gap through the affine circumcenter bridge
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

```text
kappa=1/sqrt(3000)
```

form a Kazhdan pair.

A Kazhdan pair pushes through a surjective homomorphism without tolerance
loss. Apply this first to
`LiteralBaseP13RotationQuotient.p13ToRotation_surjective`, then to
`P13CircumcenterRouteStep3.rotationToRotations_surjective`. The public word
lemmas `p13ToRotation_E12_word` through `p13ToRotation_E32_word` identify
the resulting six controls with the words in the claim.

Now let `rho` be an honest orthogonal representation of `B`, let
`||x||=1`, and suppose every element of `Q_B` moves `x` by less than
`tau`. Let `p` be the rotation-fixed projection of `x` and put
`d=||p-x||`. Applying the P13 energy estimate to the rotation-moving
projection gives

```text
d < tau/kappa.
```

The controlled translations `v2,v3` move `p` by less than `tau+2d`;
the printed rotation conjugacy gives the same estimate for `v1`. The checked
two-conjugate translation normal form therefore gives, for every translation
`a`,

```text
||rho(a)p-p|| < 2*tau+4*d.
```

The general circumcenter theorem
`P13CircumcenterRoute.exists_near_fixedSubspace_circumcenter` supplies a
translation-fixed point within `2*tau+4*d` of `p`. The translation orbit
of the rotation-fixed vector `p` is invariant under rotations, so uniqueness
of the circumcenter makes this point rotation-fixed as well. It is therefore a
globally fixed vector `y`, and

```text
||y-x|| < 2*tau+5*d
        < 2*tau+5*tau/kappa.
```

Choose

```text
tau=kappa/(2*kappa+5)=1/(5*sqrt(3000)+2).
```

The last displayed bound is strictly less than one, so `y` is nonzero. This
proves the claimed optimized affine Kazhdan pair.

Finally `S_B` has at most `17` elements. The standard Kazhdan orbit-average
estimate gives contraction

```text
1-kappaB^2/(4*|S_B|) <= 1-kappaB^2/68.
```

The fallback constant in the claim follows by instead unfolding
`ExactHodgeCertificate.certifiedKazhdanTolerance` at `c=1/250`, `r=1/500`,
and six generators, then applying the same two quotient maps and the existing
hard-coded `/64` affine bridge.
