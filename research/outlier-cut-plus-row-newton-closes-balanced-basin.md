---
rg: 2
id: outlier-cut-plus-row-newton-closes-balanced-basin
kind: route
title: Quarantine the common outlier cut and run square-function Newton on its complement
target: complete-pair-overlay-uniform-hs-basin-capture
requires:
  - quadratic-overlay-has-uniform-linearized-synchronization-gap
  - balanced-overlay-common-reducing-outlier-cut
  - balanced-overlay-diffuse-square-function-newton
---

The common cut pays the sparse high-operator-norm sector at vanishing trace
and average squared displacement.  The diffuse theorem corrects the
complement using the established uniform Jacobian transversality and the
operator row/column bound.  Fill the reducing outlier block with scalar code
characters, which exist in every dimension, and combine the two exact
blocks.  Their total normalized-HS correction gives the basin modulus.
