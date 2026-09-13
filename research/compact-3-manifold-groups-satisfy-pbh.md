---
rg: 2
id: compact-3-manifold-groups-satisfy-pbh
kind: claim
title: The fundamental group of every compact 3-manifold lies in the permutational Boone--Higman class
distinct_from:
  boone-higman-conjecture: that quantifies over all finitely generated groups with solvable word problem; this is the class of compact 3-manifold groups, which have solvable word problem.
  three-manifold-groups-pbh-off-nonfibered-graph-manifolds: that is the established part, everything except one family of closed graph manifolds; this is the full statement.
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

**OPEN.** For every connected compact 3-manifold `N`, `pi_1(N)` is in `B_A`,
the class of `boone-higman-type-a-class-closed-under-finite-extensions`. In
particular it embeds in a finitely presented simple group.

**Status.** `three-manifold-groups-pbh-off-nonfibered-graph-manifolds` proves
this except when a prime summand of the orientation cover is a closed graph
manifold with non-trivial JSJ decomposition that is not virtually fibered. That
case is `nonfibered-closed-graph-manifold-groups-satisfy-pbh`. The route
`compact-3-manifold-pbh-via-nonfibered-graph-case` combines them.
