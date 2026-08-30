---
rg: 2
id: stw99-problem-lxxvii-proper-image-map-oinfty-stable
kind: claim
title: Finite nuclear dimension and properly infinite image force O-infinity-stability (STW LXXVII)
root: true
artifacts:
  - research/artifacts/stw77-map-oinfty-audit-2026-08-30.md
---

Let `A,B` be unital C-star algebras, with `A` separable and exact, and let
`phi:A->B` be a unital homomorphism of finite nuclear dimension.  If every
nonzero positive element of `phi(A)` is properly infinite in `B`, then there
is a unital embedding

```text
O_infinity -> B_omega intersect phi(A)';
```

equivalently, `phi` is O-infinity-stable.

This is **STW Problem LXXVII and is open at the 2026-08-30 audit boundary**.

Arbitrary codomain size is now eliminated:
`stw77-counterexamples-reflect-to-separable-codomains` proves that every
failure reflects to a separable unital subalgebra containing the range,
without increasing the nuclear dimension or losing proper infiniteness of
any nonzero range positive.  Hence both `A` and `B` may be assumed separable
when searching for a counterexample.

## Attempts

- `oinfty-map-stability-is-central-isometry-splitting` gives an exact
  quantitative reduction.  The hypothesis makes `1_B` properly infinite,
  so two orthogonal isometries exist in `B`; the missing assertion is that
  such pairs can be chosen with arbitrarily small commutators with any fixed
  finite subset of `phi(A)`.
- `stw77-af-range-maps-are-oinfty-stable` proves the problem when the range is
  AF.  It splits minimal projections in a local finite-dimensional model and
  transports the splittings through matrix units.
- `stw77-bounded-operator-target-case` proves the problem for `B=B(H)` with
  no nuclear-dimension assumption.  Here pointwise proper infiniteness makes
  the range representation essential, and Voiculescu absorption produces
  central isometries without splitting outgoing color supports.
- `stw77-comparison-product-quotients-solve-map` proves much more for an
  arbitrary product of unital simple targets with almost-unperforated Cuntz
  semigroups.  Proper infiniteness of the product unit makes every factor
  strongly purely infinite.  The uniform contraction characterization then
  makes the entire product strongly purely infinite, and the same inequalities
  pass to every nonzero quotient, including quotients with no coordinate
  description.  Hence every nuclear map from a separable exact domain into
  any such quotient is strongly O-infinity-stable.  For this class the unit
  alone suffices; finite nuclear dimension is used only to supply nuclearity
  of the map.
- `stw77-properly-infinite-colored-centralizer-fusion` is a local, uniform
  finite-color statement which would solve the problem.  Its key unresolved
  step is fusion across the noncommuting order-zero colors.
- The naive plan of splitting the supports of the outgoing order-zero maps is
  invalid: those supports need not belong to `phi(A)`, and
  `proper-infinity-does-not-descend-to-color-supports` gives the elementary
  obstruction already inside `B(H)`.
- At nuclear dimension zero the support issue is now exact.
  `stw77-fd-commutant-splitting-iff-proper-supports` proves that the commutant
  of a finite-dimensional model contains two orthogonal isometries exactly
  when each minimal block projection is properly infinite.  Consequently
  `stw77-proper-support-models-force-oinfty-stability` solves every zero-color
  instance admitting such models.  What remains is selection or fusion of
  the finite-support junk blocks, not an estimate inside the model commutant.
  In particular, there is no junk obstruction when every nonzero projection
  of `B` is properly infinite:
  `stw77-zero-maps-into-projectionwise-proper-targets` proves O-infinity
  stability for every nuclear-dimension-zero unital map into such a target,
  even without the problem's pointwise image hypothesis.
- `stw77-hypotheses-and-stability-descend-to-quotients` allows quotient
  localization.  In particular, failure in any codomain quotient detects
  failure of the original map, but non-stability need not survive in some
  quotient automatically.
- Taking `A=B` and `phi=id` contains the finite-nuclear-dimensional case of
  pure infiniteness versus strong pure infiniteness, so a general proof must
  overcome rather than bypass the non-simple central-sequence obstruction.
