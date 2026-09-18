---
rg: 2
id: edge-split-sync-via-totally-irrational-shared-rays
kind: route
title: Synchronization of edge-split cells in rank m+1 follows from the shared-ray property at totally irrational directions in ranks three to m+1
target: unimodular-cells-synchronize-under-edge-splits
requires:
  - edge-split-sync-reduces-to-totally-irrational-shared-rays
  - edge-split-cells-share-rays-at-totally-irrational-directions
---

Lane bh-major-mcg-2, 2026-09-18.

1. **The reduction.** By `edge-split-sync-reduces-to-totally-irrational-shared-rays`,
   `(TI_2) ∧ … ∧ (TI_m)` implies `(LSync_m)`, and `(LSync_m)` is equivalent to
   `(Sync_m)`.
   - At a direction with a rational constraint, the reduction proceeds in three
     steps: a face cut into the rational hull, a link lift into the quotient, and the
     face lemma to glue them.
   - At a totally irrational direction, it uses the shared ray given by `(TI_m)` and
     lifts a common link descendant, with least lifts converging to the exit point.
2. **The input.** `edge-split-cells-share-rays-at-totally-irrational-directions`,
   applied in every rank `3, …, m + 1`.
3. **Conclusion.** `(Sync_m)`.

For `m = 6g − 7` this is the directedness input of the Stein–Farley set-up of
`rational-projective-full-groups-are-finitely-presented` for the closed-surface
host of genus `g`. The other inputs of that set-up are not touched:
- cofinality, which is proved (`edge-splits-cut-every-rational-hyperplane`);
- descending-link connectivity, which is open.
