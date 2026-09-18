---
rg: 2
id: thompson-t-centralizers-of-orbit-free-subgroups-act-freely
kind: claim
title: In Thompson's group T, an element commuting with a subgroup that has no finite orbit on the circle has no fixed point unless it is trivial
distinct_from:
  finite-subgroups-of-thompson-t-are-cyclic: that says finite subgroups of T act freely and are cyclic, a torsion statement; this says that the centralizer of any subgroup without finite orbits acts freely, and it uses the finitely many breakpoints of elements of T, which fails for general circle homeomorphisms
---

Let `A ≤ T` be a subgroup with no finite orbit on `S^1 = R/Z`, and let
`c ∈ T` commute with every element of `A`. If `c` has a fixed point, then
`c = 1`.

So every nontrivial element of the centralizer `C_T(A)` acts on `S^1`
without fixed points.

The piecewise-linear hypothesis is needed. In `Homeo+(S^1)` one can blow up one orbit of
the standard action of `T` into intervals (Denjoy style), extend the action
affinely across the inserted intervals, and let a nontrivial homeomorphism of
`[0,1]` act inside every inserted interval, transported along the orbit. This
commutes with the blown-up copy of `T`, has fixed points, and is nontrivial.

Derivation: route `thompson-t-centralizers-of-orbit-free-subgroups-act-freely-proof`.
