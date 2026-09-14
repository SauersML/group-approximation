---
rg: 2
id: gottschalk-via-dual-surjunctivity-and-decoder-transfer
kind: route
title: Prove the dual conjecture for every group and transfer it to surjunctivity through post-surjective decoders
target: gottschalk-surjunctivity-conjecture
requires:
  - every-group-is-dual-surjunctive
  - dual-surjunctive-groups-are-surjunctive
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

1. If every group is dual surjunctive (`every-group-is-dual-surjunctive`), and
2. every dual surjunctive group is surjunctive
   (`dual-surjunctive-groups-are-surjunctive`),
3. then every group is surjunctive.

The second prerequisite reduces, through
`dual-surjunctive-surjunctive-via-post-surjective-decoders`, to one existence
step: `strict-pairs-admit-post-surjective-decoders`.
