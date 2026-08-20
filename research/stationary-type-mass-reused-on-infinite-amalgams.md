---
rg: 2
id: stationary-type-mass-reused-on-infinite-amalgams
kind: claim
title: Infinite free amalgams reuse stationary representation-type mass instead of dispersing it on the Bass-Serre tree
invalidates:
  - multiplicity-return-via-free-amalgam
distinct_from:
  finite-graph-of-groups-representation-types-are-integer-flows: that describes compatible type vectors for a finite graph; this proves that passing to an infinite tree does not add an ell2 summability condition or remove a compatible scalar ray.
  bass-serre-schur-transfer-contraction: that may still ask for transverse contraction after explicitly removing the scalar ray; this proves such contraction cannot dispose of the scalar current or yield the proposed return theorem by plain amalgamation.
artifacts:
  - research/artifacts/trace-promotion-renormalization-program-2026-08-20.md
---

Let `T` be any finite or countable tree of finite groups. Suppose there is one
dimension `d` and, for every vertex `v`, a representation

```text
rho_v:G_v -> U(d)
```

such that the two restrictions at every edge are unitarily equivalent. Then
the fundamental group of the tree of groups has a `d`-dimensional
representation restricting to the prescribed type at every vertex.

No sum of vertex dimensions occurs: the same Hilbert space `C^d` is reused at
every stage. Consequently the compatible type sequence is naturally bounded
or `ell^infinity`, not `ell^2` on the Bass--Serre tree. Nonamenability of the
tree and spectral radius below one on a transverse `ell^2` sector do not force
the stationary type mass to escape or leak.

For the translation-symmetrized full Schur reset, the compatible scalar ray
of `symmetrized-reset-collapses-schur-flow-to-one-ray` supplies exactly such a
stationary representation at every repeated stage after passing to a common
multiple of the fixed packet dimensions. Hence an infinite iterated free
amalgam does not remove the regular scalar-flow countermodel. Any successful
return must impose orthogonal range branching, a proper corner, a projective
cocycle, or another relation beyond plain Bass--Serre amalgamation.
