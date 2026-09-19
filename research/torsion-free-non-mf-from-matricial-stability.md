---
rg: 2
id: torsion-free-non-mf-from-matricial-stability
kind: route
title: Stability plus no finite-dimensional representations on the torsion-free group
target: torsion-free-finitely-presented-non-mf
requires: [map-matricial-stability-non-mf, fournier-facio-group-finite-dimensional-shadow, defect-normally-generates-torsion-free-quotient, fournier-facio-group-matricially-stable]
---

## Why sufficient

Let `G` be the Fournier-Facio group: finitely presented, torsion-free,
Kazhdan, infinite.

`defect-normally-generates-torsion-free-quotient` in its strong form gives
`<<pi(S)>> = G`, and then
`fournier-facio-group-finite-dimensional-shadow` clause 3 makes `G`
minimally almost periodic.  With
`fournier-facio-group-matricially-stable`,
`map-matricial-stability-non-mf` applies and `G` is not MF — indeed every
corona representation of `G` is trivial.

This route shares its group-theoretic prerequisite with the primary route
`torsion-free-non-mf-from-normal-kazhdan-defect` and differs only in the
analytic one, where it substitutes a named stability property for the
repository's own normal-Kazhdan obstruction.  It is therefore a genuine
alternative rather than a variant: if the small-cancellation prerequisite
lands and the normal-Kazhdan obstruction turns out to have a gap, this route
still reaches the root, and vice versa.

The cost is that its analytic prerequisite is strictly stronger than
necessary — matricial stability of `G` would prove far more than
non-MF-ness — and that it is unproved for every candidate.  The primary
route remains the one to back, because its analytic half is already
machine-checked.
