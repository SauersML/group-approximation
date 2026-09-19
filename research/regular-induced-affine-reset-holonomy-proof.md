---
rg: 2
id: regular-induced-affine-reset-holonomy-proof
kind: route
title: Induce six one-direction Clifford reset cells over the regular S3 orbit
target: regular-induced-affine-reset-synchronizes-s3-holonomy
requires:
  - every-predicate-has-s3-equivariant-raw-radical-drop
  - gauge-doubling-gives-selector-flip-symmetries
  - fanizza-schur-menu-has-common-codimension-one-residual
  - derived-lifted-gauge-reset-spin-bridge
  - s3-reset-plane-has-common-invariant-selector-polarization
  - regular-orbit-induction-coherifies-finite-edges
  - regular-clifford-edge-map-has-zero-kernel
---

Apply regular-orbit induction to the six reparameterized copies of the
one-direction edge.  Componentwise equality of the old/fresh
`2 rho_15` restriction gives the equal-scale product edge, and left
translation supplies the `S_3` action.  Gauge doubling keeps all logical
products fixed while the private shares and dummy/residual factors are
permuted.  The general equivariant-edge theorem then identifies the six
directional multiplicity transports as conjugates of one stable word.

The presentation-level hypothesis of regular induction is not inferred from
those restriction dimensions.  `regular-clifford-edge-map-has-zero-kernel`
checks the complete class-two Schur and balanced-dummy presentations, proves
the component maps injective, and checks the regular semidirect map has zero
kernel.  Its `150`-dimensional quotient obstruction also shows why the six
residual packets must remain private even though their logical gauge-share
products are common.
