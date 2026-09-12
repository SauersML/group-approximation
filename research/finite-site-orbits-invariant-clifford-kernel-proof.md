---
rg: 2
id: finite-site-orbits-invariant-clifford-kernel-proof
kind: route
title: Pass finite site orbits through Clifford words and local finiteness
target: finite-site-orbits-invariant-clifford-kernel
requires: []
artifacts:
  - GroupApproximation/Sofic/FiniteOrbitInvariantKernel.lean
---

## Why sufficient

For any action by automorphisms, the elements having finite orbit form a
subgroup: the orbit of a product is contained in the product of the two
finite orbits, and inversion preserves finiteness.  The central Clifford
sign is fixed, while the orbit of a lamp is the image of its site's orbit.
The presentation's generator-elimination principle therefore puts every
Clifford-lamp element in the finite-orbit subgroup.

For a finite window, take the finite union of its element-orbits and close
it under the group law.  That generating set is invariant.  Local finiteness
of the Clifford lamp group places its closure inside a finite subgroup, so
the closure itself is finite and supplies the required invariant subgroup.
