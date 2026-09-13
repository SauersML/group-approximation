---
rg: 2
id: thompson-f-not-automatic-via-finite-cd
kind: route
title: If torsion-free automatic groups have finite cohomological dimension, Thompson's group F is not automatic
target: thompson-f-is-not-automatic
requires:
  - torsion-free-automatic-groups-have-finite-cd
  - thompson-f-has-infinite-cohomological-dimension
---

`F` is torsion-free with `cd F = ∞` (`thompson-f-has-infinite-cohomological-dimension`).
If `F` were automatic, `torsion-free-automatic-groups-have-finite-cd` would give
`cd F < ∞`. So `F` is not automatic.

The prerequisite is a universal statement about automatic groups and is not
equivalent to the target: it can fail while `F` is still non-automatic, so this
is a reduction and not a restatement.
