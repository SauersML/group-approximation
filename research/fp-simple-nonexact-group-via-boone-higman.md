---
rg: 2
id: fp-simple-nonexact-group-via-boone-higman
kind: route
title: Embed the decidable non-exact simple Kazhdan LEF group in a finitely presented simple group
target: fp-simple-nonexact-group
requires: [boone-higman-conjecture, decidable-residually-finite-non-exact-group-exists, exact-groups-are-closed-under-extensions]
artifacts:
  - research/artifacts/exactness-boone-higman-separator-2026-09-17.md
---

1. By `decidable-residually-finite-non-exact-group-exists`, some finitely generated group `G` with solvable word problem is not exact. Osajda's residually finite group is one.
2. By `boone-higman-conjecture` (OPEN), `G ≤ K` for some finitely presented simple group `K`.
3. Closed subgroups of exact groups are exact (`exact-groups-are-closed-under-extensions`). So `K` is not exact.

∎ The only open prerequisite is the conjecture itself. This is the contrapositive half of `exactness-separates-boone-higman-iff-fp-simple-groups-exact`.
