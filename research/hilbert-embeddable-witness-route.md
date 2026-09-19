---
rg: 2
id: hilbert-embeddable-witness-route
kind: route
title: Convert a Hilbert embeddable weak-soficity witness into unitary microstates
target: hyperlinear-nonsofic-group
requires: [hilbert-embeddable-length-hyperlinearity, hilbert-embeddable-witness-for-kun-thom-wreath, kun-thom-nonsofic-wreath]
---

## Why sufficient

Kun--Thom Theorem A makes `W=(directSum_(G/Gamma)Z/2Z) semidirect G`
nonsofic for the explicit residually finite Kazhdan pair of their Theorem E.
If `W` admits weak-soficity witnesses with Hilbert embeddable invariant
lengths, the Schoenberg realization makes `W` hyperlinear.  A hyperlinear
group that is not sofic is the program target.

This route is independent of the Clifford and crossed-product lanes: it
needs no von Neumann algebra, no Connes embeddability statement, and no
control of the coset action.  That last point is the reason to run it.
Every hyperlinear wreath-permanence theorem in the literature — Hayes--Sale,
Holt--Rees, Gao--Kunnawalkam Elayavalli--Patchell, Alekseev--Bradford
Definition 4.23 — models the action by permutations of a finite set, which
Kun--Thom Corollary D forbids here; Glebsky's permanence theorem has no
hypothesis on the action at all, and this route is the attempt to inherit
that freedom on the unitary side.
