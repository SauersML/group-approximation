---
rg: 2
id: stw99-lxxvi-strong-pure-infiniteness-implies-cu-regularity
kind: claim
title: Strong pure infiniteness implies Cuntz-semigroup regularity
distinct_from:
  stw99-lxxvi-locally-subhomogeneous-positive-class: that is a stably finite zero-dimensional theorem using stable rank one and Z-stability; this is a traceless ideal-lattice collapse with no stable-rank or nuclearity hypothesis.
  stw99-lxxvi-one-dimensional-formation-preserves-cu-regularity: that computes Cu of continuous fields under stable-rank-one and idealwise K1 hypotheses; this applies directly to arbitrary separable strongly purely infinite algebras and imposes no condition on their primitive spaces.
  stw99-lxxvi-first-factor-map-has-identical-coarse-shadows: that only identifies ideal lattices and warns that this is insufficient in general; strong pure infiniteness makes the ideal lattice the entire Cuntz semigroup, so the coarse shadow becomes complete.
artifacts:
  - research/artifacts/stw99-lxxvi-strong-pure-infiniteness-audit-2026-08-30.md
---

Every separable strongly purely infinite C\*-algebra `A` is pure and Cuntz
semigroup regular.  Thus the first-factor embedding

```text
iota_A:A -> A tensor_min Z
```

induces an isomorphism

```text
Cu(iota_A):Cu(A) -> Cu(A tensor_min Z).
```

More generally, the same conclusion holds for every separable purely
infinite `A` for which `A tensor_min Z` is purely infinite.  Strong pure
infiniteness guarantees the latter hypothesis because `Z` is exact.

No nuclearity, stable rank one, finite-dimensional approximation, or
Z-absorption assumption is used.  This gives a purely infinite positive
class for STW Problem LXXVI complementary to the existing stably finite
continuous-field classes.
