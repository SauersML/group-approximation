---
rg: 2
id: tree-braid-sigma-for-at-most-three-strands-and-radial-trees
kind: claim
title: "BNSR invariants of tree braid groups on at most three strands and of radial tree braid groups: all of S^0 exactly for two points on a triod, otherwise empty"
distinct_from:
  two-strand-braid-groups-of-k5-and-k33-have-empty-sigma: that claim covers two non-planar graphs whose 2-strand braid groups are surface groups; this one covers all trees with n <= 3 and all radial trees, whose braid groups are free
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part3.md
---

Let `T` be a finite tree.

- `n = 2`: `B_2T` is free of rank `Σ_v C(deg v − 1, 2)`. `Σ^m(B_2T) = S⁰`
  for all `m` iff `T` is a subdivided triod (one essential vertex, of
  degree 3). If `T` is an arc there are no characters. Otherwise
  `Σ^m(B_2T) = ∅` for all `m`.
- `n = 3`: if `T` is not an arc, `Σ^m(B_3T) = ∅` for all `m`.
- `T` radial with essential vertex of degree `d`, `n ≥ 2`: `B_nT` is free of
  rank `1 − C(n+d−1, d−1) + (d−1)C(n+d−2, d−1)`, and `Σ^m(B_nT)` is `S⁰` iff
  `(d, n) = (3, 2)`, otherwise `∅`.

This is the complete computation of Problem 1.8 for these families.
Unreviewed.
