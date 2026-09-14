---
rg: 2
id: lot-reductions-preserve-homotopy-type
kind: claim
title: Compression, boundary reduction and interior folding of a LOT preserve the homotopy type of its complex
distinct_from:
  lot-collapsed-maximal-sub-lot-test-transfers-asphericity: that transfers asphericity from a sub-LOT through a directed DR condition; this says the three elementary reductions do not change the homotopy type at all.
---

Every labeled oriented tree `G` can be transformed into a reduced LOT `G_red` by
three moves, each a 3-deformation of complexes, so `K(G) ≃ K(G_red)`:

- *compression*: an edge `[a, a, b]` or `[b, a, a]` is removed, `a` and `b` are
  identified to `a`, labels `b` become `a`;
- *boundary reduction*: an edge at a boundary vertex `a` that is not a label is
  removed together with `a`;
- *interior folding*: two edges `[a, d, b]`, `[c, d, b]` (or `[b, d, a]`, `[b, d, c]`)
  are folded, `a` and `c` identified to `a`, labels `c` become `a`.

Imported; see `lot-reductions-citation`.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/hl-whitehead-relative-pins-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
