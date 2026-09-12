---
rg: 2
id: fpbs-group-invariance-via-product-moves
kind: route
title: Chain single product-generator moves between any two generating sets
target: fpbs-nonuniqueness-phase-is-a-group-invariant
requires:
  - fpbs-gap-survives-product-generator-moves
  - fpbs-generating-sets-connected-by-product-moves
artifacts:
  - research/artifacts/fpbs-choi-seo-q12-invariance-2026-09-12.md
---

Let `S` have `p_c < p_u`, and let `S'` be any other finite symmetric generating
set not containing `e`.

1. By `fpbs-generating-sets-connected-by-product-moves`, there is a finite
   sequence `S = S_0, S_1, ..., S_n = S'` in which each step is one Add or
   Remove move.
2. By `fpbs-gap-survives-product-generator-moves`, applied inductively, each
   `S_i` has `p_c < p_u`.
3. So `S'` has `p_c < p_u`.

The converse holds trivially, because each move produces a generating set of the
same group. It is not wired as a route, to avoid a dependency cycle.
