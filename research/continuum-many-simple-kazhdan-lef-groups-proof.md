---
rg: 2
id: continuum-many-simple-kazhdan-lef-groups-proof
kind: route
title: Each abstract isomorphism class sees only countably many markings, hence only countably many subshifts
target: continuum-many-simple-kazhdan-lef-groups
requires: [marked-subshift-elementary-group-determines-language, continuum-many-infinite-minimal-binary-subshifts, simple-kazhdan-lef-group-from-minimal-subshift]
artifacts:
  - research/artifacts/un-open-5-marked-subshift-groups-2026-09-13.md
---

Artifact §4.
1. Fix `q` and the alphabet `{0,1}`. By `simple-kazhdan-lef-group-from-minimal-subshift`, each `S_X` is infinite,
   finitely generated, simple, Kazhdan and LEF. It has no nontrivial finite quotient, since it is simple and
   infinite.
2. Let `φ : S_X → H` be an isomorphism and `t = φ(σ_X) ∈ H^I`. Then `W_w(t) = φ(W_w(σ_X))`, so
   `L(X) = {w : W_w(t) ≠ 1}` (`marked-subshift-elementary-group-determines-language`). So distinct `X` with
   `S_X ≅ H` give distinct tuples `t`. `H` is countable and `I` is finite, so at most countably many `X` have
   `S_X ≅ H`.
3. There are continuum many infinite minimal binary subshifts (`continuum-many-infinite-minimal-binary-subshifts`).
   A continuum is not a countable union of countable sets, so the `S_X` realize continuum many isomorphism types.
