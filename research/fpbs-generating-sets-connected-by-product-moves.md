---
rg: 2
id: fpbs-generating-sets-connected-by-product-moves
kind: claim
title: Any two finite symmetric generating sets are joined by moves that add or remove one product of two generators
distinct_from:
  fpbs-nonuniqueness-phase-is-a-group-invariant: that is a percolation statement about all generating sets; this is a purely combinatorial fact about how generating sets are connected, with no percolation content.
artifacts:
  - research/artifacts/fpbs-choi-seo-q12-invariance-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma` be a finitely generated group. Call a finite
symmetric generating set not containing `e` *admissible*. There are two moves:

- **Add:** `S -> S ∪ {t, t^{-1}}` with `t = uv`, `u, v in S`, and
  `t ∉ S ∪ {e}`.
- **Remove:** `S -> S \ {t, t^{-1}}` with `t in S`, `t = uv`, and
  `u, v in S \ {t, t^{-1}}`.

Both moves take admissible sets to admissible sets. Any two admissible
generating sets of `Gamma` are joined by a finite sequence of moves.

The proof builds geodesic prefixes and removes elements in decreasing word
length. It is in `fpbs-generating-sets-connected-by-product-moves-proof`, and in
Section 3 of the artifact.
