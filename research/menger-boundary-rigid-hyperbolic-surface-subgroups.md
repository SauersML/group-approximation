---
rg: 2
id: menger-boundary-rigid-hyperbolic-surface-subgroups
kind: claim
title: Every rigid hyperbolic group whose boundary is the Menger curve contains a surface subgroup
distinct_from:
  random-groups-below-density-half-contain-surface-subgroups: that finds surface subgroups in random groups with overwhelming probability; this asks for every rigid hyperbolic group with Menger curve boundary
  carpet-boundary-hyperbolic-groups-have-surface-subgroups: that is the planar one-dimensional case, where peripheral circles supply finite-by-Fuchsian stabilizers; the Menger curve has no canonical countable family of circles to play that role
  rigid-hyperbolic-groups-contain-surface-subgroups: that is the whole rigid case; this is its one-dimensional non-planar part
---

**OPEN.** Let `R` be a hyperbolic group whose Gromov boundary is homeomorphic to the Menger curve,
and which admits no nontrivial splitting over a finite or virtually cyclic subgroup. Then `R`
contains a subgroup isomorphic to the fundamental group of a closed surface with `chi < 0`.

This is the Menger alternative (1) of Kapovich--Kleiner Theorem 4 in
`kapovich-kleiner-one-dimensional-boundary-classification`.

## Attempts

- **Carpet argument.** It dies on non-planarity. For a carpet, Kapovich--Kleiner Section 2
  identifies the peripheral circles as the nonseparating circles. Theorem 8 then shows that the
  finitely many orbits of them have quasiconvex stabilizers, which are virtually Fuchsian. Every
  point of the Menger curve lies on nonseparating circles, and there is no canonical countable
  family. A circle in `∂R` whose stabilizer acts cocompactly on it is exactly what a quasiconvex
  surface subgroup would provide, so one would have to find such a circle.
- **Random groups.** Random groups at density `< 1/2` are expected to be examples. Their boundary
  is reported to be the Menger curve by Dahmani--Guirardel--Przytycki (second-hand, unverified).
  They contain surface subgroups by `random-groups-below-density-half-contain-surface-subgroups`,
  but only with overwhelming probability, so this is evidence rather than a proof.
- **Hierarchies.** Cubulated descent via Wilton, arXiv:2406.02121, produces one-ended quasiconvex
  subgroups of infinite index, not surface subgroups, and the iteration has no termination
  argument.
- **KMS families.** Their boundary type was not checked, so it is unknown whether the certified
  genus-two subgroups in the `kms-*` claims fall in this case.
