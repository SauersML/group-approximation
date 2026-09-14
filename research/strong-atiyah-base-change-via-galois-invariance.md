---
rg: 2
id: strong-atiyah-base-change-via-galois-invariance
kind: route
title: Apply the Galois-invariance base change to every torsion-free group
target: strong-atiyah-base-change-algebraic-to-complex
requires:
  - strong-atiyah-base-change-from-galois-invariance
  - vn-rank-galois-invariant-for-torsion-free-groups
---

Assume Strong Atiyah over `Qbar` for every torsion-free group.  For a
torsion-free `G`, every `G x Z^r` is torsion-free.  So it satisfies Strong
Atiyah over `Qbar` by assumption, and has Galois-invariant kernel dimensions
by [[vn-rank-galois-invariant-for-torsion-free-groups]].
[[strong-atiyah-base-change-from-galois-invariance]] then gives Strong Atiyah
over `C` for `G`.

Not a restatement: the invariance prerequisite asserts no integrality, and the
target does not assert invariance.
