---
rg: 2
id: finite-augmentation-wreath-partial-rotation-proof
kind: route
title: Cut a shift into orthogonal augmentation sectors and rotate the resulting matrix units
target: finite-augmentation-corner-has-outside-normalizer-contexts
requires:
  - noncentral-frobenius-negative-corner-is-rational-matrix-algebra
  - lin-explicit-fixed-bcs-gap-via-generic-conversion
artifacts:
  - research/artifacts/finite-augmentation-outside-normalizer-two-context-cell-2026-09-08.md
---

The independent lamp involutions give commuting projections
`q_i`. Their chosen products `f,r` are orthogonal and lie
under `q_0`. The shift cut `v=tf` has initial projection
`f` and final projection `r`. These identities make
`f,r,v,v^*` exact two-by-two matrix units. Their symmetric
and antisymmetric combinations are the displayed transported
PVM, and direct multiplication verifies the one common unitary
`R`. The off-diagonal matrix units give the claimed nonzero
commutator norm.

The shift quotient separates the degree-zero terms from the
nonzero degree-one and degree-minus-one coefficients. This
proves both support escape and involvement of elements outside
the finite subgroup's normalizer. Canonical coefficients compute
the positive trace of every atom.

For the limiting scope, reduce a sufficiently large finite
wreath normal-form window modulo a longer cyclic interval.
This preserves its specified products and distinct support
elements inside a finite wreath product, without claiming a
global quotient for the nonabelian lamp group. Any completed
finite BCS corner diagram would therefore give an exact
finite-dimensional corner model retaining the mark, contrary
to the fixed source gap.
