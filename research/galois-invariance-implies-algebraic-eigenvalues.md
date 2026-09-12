---
rg: 2
id: galois-invariance-implies-algebraic-eigenvalues
kind: claim
title: Galois-invariant kernel dimensions force every eigenvalue of an algebraic group-ring matrix to be algebraic
distinct_from:
  vn-rank-galois-invariant-for-torsion-free-groups: that is the open invariance statement; this is the established consequence that invariance has for point spectrum.
  integer-moment-measure-with-negative-log-determinant: that is a spectral measure with Galois-unequal algebraic atoms; this concerns atoms at transcendental points, which invariance excludes entirely.
---

Let `H` be a group whose kernel dimensions on `C[H]` are invariant under the
automorphisms of `C` fixing `Qbar`.  Then for every `X in M_n(Qbar[H])` and
every `w in C` with `ker(r_X - w) != 0`, the number `w` is algebraic.

This is the algebraic eigenvalue property.  Dodziuk--Linnell--Mathai--Schick--Yates
(arXiv:math/0107049, abstract) establish the absence of transcendental
eigenvalues when the group is amenable or in Linnell's class `C`.

**Consequence for base change.**  Every proof of Strong Atiyah over `C` through
`strong-atiyah-base-change-from-galois-invariance` also proves that torsion-free
groups have no transcendental eigenvalues over `Qbar[H]`.  That base change
itself asks less: a transcendental eigenvalue of integer multiplicity does not
contradict Strong Atiyah over `C`.

**ESTABLISHED 2026-09-12** by [[galois-invariance-algebraic-eigenvalue-proof]].
