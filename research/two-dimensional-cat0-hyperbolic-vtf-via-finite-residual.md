---
rg: 2
id: two-dimensional-cat0-hyperbolic-vtf-via-finite-residual
kind: route
title: Restrict the finite-residual reduction of hyperbolic virtual torsion-freeness to the 2-dimensional CAT(0) class
target: two-dimensional-cat0-hyperbolic-groups-virtually-torsion-free
requires:
  - finite-torsion-carrier-virtual-torsionfree-criterion
  - hyperbolic-finite-residual-is-torsion-free
---

This is the specialisation of `hyperbolic-virtual-torsionfree-via-finite-residual`.
A hyperbolic group has finitely many conjugacy classes of finite subgroups.
`finite-torsion-carrier-virtual-torsionfree-criterion` then makes virtual
torsion-freeness equivalent to torsion-freeness of the finite residual, and
`hyperbolic-finite-residual-is-torsion-free` asserts the latter for every
hyperbolic group. In particular it holds for those acting properly and
cocompactly on CAT(0) 2-complexes.
