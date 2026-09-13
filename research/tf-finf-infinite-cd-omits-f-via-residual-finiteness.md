---
rg: 2
id: tf-finf-infinite-cd-omits-f-via-residual-finiteness
kind: route
title: A residually finite infinite-dimensional torsion-free F_infinity group omits Thompson's group F
target: some-torsion-free-f-infinity-group-of-infinite-cd-omits-f
requires:
  - some-rf-torsion-free-f-infinity-group-has-infinite-cd
  - thompson-f-is-not-residually-finite
---

Let `G` be a residually finite torsion-free group of type F_∞ with `cd G = ∞`
(`some-rf-torsion-free-f-infinity-group-has-infinite-cd`). By
`thompson-f-is-not-residually-finite`, no residually finite group contains a
subgroup isomorphic to `F`, so `G` omits `F`. So `G` witnesses
`some-torsion-free-f-infinity-group-of-infinite-cd-omits-f`.

This is a genuine reduction. The prerequisite can fail without the target failing,
and it does not mention `F`. The step that recovers the target is the displacement
commutator argument that kills a fixed nontrivial element of `F` in every finite
quotient.
