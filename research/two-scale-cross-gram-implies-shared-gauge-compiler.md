---
rg: 2
id: two-scale-cross-gram-implies-shared-gauge-compiler
kind: route
title: Polar-align the two transports and apply the affine gauge-rank floor
target: binary-leavitt-two-shared-gauge-selector-compiler
requires:
  - binary-leavitt-native-two-scale-cross-gram-positive
  - two-transport-cross-gram-has-a-fixed-mass-reducing-corner
  - two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
---

Apply the fixed-mass cross-Gram cutoff to `(NCG1)` and exactify its positive
approximately reducing packet corner.  On corresponding polar subcorners,
the two packet transports differ by a source-commutant unitary.  The two
mixed Pauli estimates move that relative unitary into the common
multiplicity reservoir, so the two controlled external involutions are
conjugate on this nonzero corner up to `o(1)`.  Their positive spectral
fractions consequently differ by `o(1)`.

The fixed packet traces give the two selector ratios in `(SGS1)`.  The robust
affine rank calculation `(TSG3)--(TSG4)` now forces total normalized-HS row
defect at least `1/3-o(1)`, contradicting the microstate relations on the
positive-density carrier.  Common amplification is harmless because it
changes neither spectral fraction.
