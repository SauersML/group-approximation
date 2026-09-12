---
rg: 2
id: discrete-kazhdan-groups-are-finitely-generated-proof
kind: route
title: Apply property T to the quasi-regular representations of finitely generated subgroups
target: discrete-kazhdan-groups-are-finitely-generated
requires: []
artifacts:
  - GroupApproximation/Kazhdan/KazhdanFiniteGeneration.lean
---

Kernel-checked as
`KazhdanFiniteGeneration.exists_symmetric_generating_finset`.  Briefly, if a
discrete group `K` were not finitely generated, direct the finitely generated
subgroups `H` by inclusion and use the quasi-regular representations on
`ell^2(K/H)`.  Every prescribed finite subset of `K` fixes the delta vector
at `H` once it lies in `H`, so the resulting direct sum has almost invariant
unit vectors.  Property `(T)` produces an invariant vector in one of the
relevant quasi-regular pieces.  Such a vector is constant on the infinite
orbit `K/H`, hence cannot be nonzero in `ell^2(K/H)` unless `[K:H]` is
finite.  Enlarging `H` by finitely many coset representatives then gives a
finite generating set for `K`.
