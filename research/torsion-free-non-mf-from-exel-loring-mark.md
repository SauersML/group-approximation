---
rg: 2
id: torsion-free-non-mf-from-exel-loring-mark
kind: route
title: Pin the infinite-order mark by its Exel--Loring winding number
target: torsion-free-finitely-presented-non-mf
requires: [infinite-order-central-mark-group, exel-loring-mark-quantization]
---

## Why sufficient

`infinite-order-central-mark-group` supplies a torsion-free finitely
presented group `Gtilde` carrying the Kazhdan compression data with a
nontrivial infinite-order central mark `zeta` in the normal closure of the
compression defect.  In the Heisenberg-lamp design that mark is the
commutator of two lamp generators, so it is the value of a central extension
class on the `H_2` class represented by that single commutator relation —
which is exactly the pairing `<c, x> != 0` that
`exel-loring-mark-quantization` requires.  That claim then kills `zeta` in
every corona representation, so no corona representation is injective and
`Gtilde` is not MF, while being torsion-free and finitely presented.

This is the third analytic option for the central-mark branch, alongside
`commutant-projection-extraction` and
`kazhdan-invariant-subspace-generates`.  It is the only one of the three
whose main tool is published rather than to be invented, and it attacks the
near-scalar case that `corona-corner-detection-criterion` leaves open — but
it carries two identified blockers, both recorded in the claim body, and it
is a programme rather than a proof.
