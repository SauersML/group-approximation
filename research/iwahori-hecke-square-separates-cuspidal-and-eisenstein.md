---
rg: 2
id: iwahori-hecke-square-separates-cuspidal-and-eisenstein
kind: claim
title: A fixed Hecke-square operator separates the algebraic cuspidal and Eisenstein spectra by one half
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-cuspidal-hecke-angle: that bounds the two degeneracy maps on the cuspidal sector; this separates the cuspidal sector from boundary cohomology in the native cellular Hodge norm.
  iwahori-eisenstein-angle: that computes the two-vertex residue mismatch; this is a one-vertex spectral projection separating boundary classes from interior classes.
---

**ESTABLISHED (algebraic spectral statement only).**  Let `N` be an odd
congruence subgroup of `SL_2(Z)` and let `E` be a finite-rank unitary
congruence local system.  On `H^1(N,E)` let `T_2` be the unnormalised Hecke
correspondence at `2` and let `<2>` denote the central (diamond)
correspondence.  For the fixed operator

```text
K_2 := T_2^2 / (2 <2>)                                  (HS1)
```

the algebraic spectrum on cuspidal cohomology lies in `[0,4]`, whereas its
algebraic spectrum on Eisenstein cohomology lies on the ellipse

```text
{2+(5/2) cos(theta)+(3/2)i sin(theta): theta in R}.       (HS2)
```

The ellipse and `[0,4]` are at distance exactly `1/2`.  This separation is
uniform in the congruence level, coefficient representation, and dimension.

The statement remains true after taking deck-group isotypic components and
for Iwahori-fixed vectors, using the corresponding central element of the
affine Iwahori Hecke algebra.  Thus it applies directly to `E=Ad rho` after
passing to an odd principal kernel on which `rho` is trivial.

**Important limitation.**  Algebraic spectral separation does not by itself
bound the cellular-Hodge spectral projections of a nonnormal operator.  The
uniform Riesz-projector estimate is exactly the remaining content of
`iwahori-parabolic-boundary-splitting-is-uniform`; it is not claimed here.
