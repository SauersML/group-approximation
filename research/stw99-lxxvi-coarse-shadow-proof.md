---
rg: 2
id: stw99-lxxvi-coarse-shadow-proof
kind: route
title: Use simplicity of Z, its KK equivalence with the scalars, and quasitrace invariance
target: stw99-lxxvi-first-factor-map-has-identical-coarse-shadows
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Because `Z` is simple and nuclear, the slice-map theorem identifies the
closed ideals of `A tensor_min Z` exactly as `I tensor_min Z`, naturally in
`I`.  The inverse sends an ideal `L` to the closed span of its slices
`(id tensor omega)(L)`.

The unital inclusion `C -> Z` is a KK-equivalence.  Exterior product with
`A` makes `iota_A` a KK-equivalence, and hence gives the asserted
isomorphisms on both K-groups.

Finally, STW Lemma 22(i) proves directly that restriction along `iota_A`
is an affine homeomorphism on the cones of densely defined lower
semicontinuous 2-quasitraces.  These three statements concern the actual
first-factor embedding, not merely an abstract identification of its source
and target invariants.
