---
rg: 2
id: robertson-steger-tile-groupoids-have-no-spatial-realization
kind: claim
title: The path groupoid of a Robertson-Steger A2 tile 2-graph has no spatial realization in any Cuntz product groupoid G_2^n
artifacts:
  - research/artifacts/nv-bernoulli-conformal-class-kill-2026-09-17.md
distinct_from:
  cmsz-pg22-rs-two-graphs-admit-no-brick-coding: that excludes edge-wise brick codings of five explicit tile 2-graphs; this excludes every continuous groupoid homomorphism that is a homeomorphism on units, for all q.
  spatial-two-graph-realizations-in-g2n-leave-the-degree-plane: that is the unconditional obstruction theorem; this is its application to Robertson-Steger tile groupoids, conditional on cocycle rigidity.
---

**OPEN.** Let `T` be a triangle presentation over `PG(2,q)` satisfying (A1)–(A3), and let
`Λ_T` be its tile 2-graph.

**Claim.** There is no continuous groupoid homomorphism `ι : G_{Λ_T} -> G_2^n` whose
restriction to the unit space is a homeomorphism onto a compact open subset of
`({0,1}^N)^n`, for any `n`.

**Consequence for the target.** In
`some-brin-thompson-group-has-an-infinite-kazhdan-subgroup`, every realization of
`[[Λ_T]] ↪ nV` obtained by conjugating through such an `ι` dies. This covers brick codings
of `Λ_T` and of all its block recodings, for every `q`.

Route: `robertson-steger-no-spatial-realization-via-rigidity`. Its only OPEN input is
`robertson-steger-two-graph-groupoids-are-cocycle-rigid`.
