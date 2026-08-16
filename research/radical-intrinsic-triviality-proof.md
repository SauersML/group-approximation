---
rg: 2
id: radical-intrinsic-triviality-proof
kind: route
title: The radical sits inside a restricted direct sum of finite groups
target: invisible-radical-is-intrinsically-visible
requires: [compression-wreath-five-radicals-coincide]
artifacts:
  - GroupApproximation/Algebra/PermutationalWreath.lean
---

## Why sufficient

The telescope map is the identity on the `G*` coordinate, so its kernel
`R_K` lies inside the lamp base `K^(G*/Gamma*)`.  Any finitely generated
subgroup of a restricted direct sum of copies of a finite group is supported
on the finite union of the supports of its generators, hence is contained in a
finite direct product and is finite.  So the lamp base, and therefore `R_K`,
is locally finite; local finiteness gives amenability directly, since a
finitely generated subgroup is a Folner set for its own generating set.

Residual finiteness: a nontrivial finitely supported configuration is
separated by projection to a site where it is nontrivial, landing in the
finite group `K`.  Those finite quotients separate all points, so all five
intrinsic residuals of `R_K` vanish — the regular representations of the
finite quotients are simultaneously finite-dimensional unitary, linear over
every field, compact, and constant-sequence corona representations.

Nontriviality of `R_K` and its identification with the five ambient residuals
are the prerequisite.  `PermutationalWreath.lean` carries the local
finiteness (`suppIn_finite`), residual finiteness
(`lamp_isResiduallyFinite`), amenability, and linearity of the lamp group at
kernel level.
