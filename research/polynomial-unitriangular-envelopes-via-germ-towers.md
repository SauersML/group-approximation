---
rg: 2
id: polynomial-unitriangular-envelopes-via-germ-towers
kind: route
title: Embed polynomial unitriangular lamps in the clopen actor and apply the classical twisted Brin–Thompson construction
target: polynomial-unitriangular-lamps-have-simple-f-infinity-hosts
requires:
  - polynomial-valuation-germ-towers-are-f-infinity
  - polynomial-germ-clopen-action-structure
  - polynomial-unitriangular-lamps-embed-in-polynomial-germ-groups
artifacts:
  - research/artifacts/polynomial-germ-unitriangular-manuscript-2026-09-20.md
---

The third prerequisite embeds the source in `B_{d,2}`. The first gives
type `F_∞` for every restriction group appearing in the second, and
finite products and finite extensions give type `F_∞` for all finite
clopen-subset stabilizers. The actor is faithful and oligomorphic.
Use Belk–Zaremsky, arXiv:2001.04579, Theorem D and the manuscript's
cited Theorem 3.4 for the simple `F_∞` host with two finite-order
generators. These are explicit classical dependencies; no corresponding
Lean proof is asserted. All three new prerequisites remain OPEN.
