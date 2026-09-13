---
rg: 2
id: tree-braid-sigma-small-strands-and-radial-trees-proof
kind: route
title: "Freeness plus Euler characteristic ranks give the BNSR invariants of small tree braid groups"
target: tree-braid-sigma-for-at-most-three-strands-and-radial-trees
requires:
  - tree-braid-groups-with-at-most-three-strands-are-free
  - radial-tree-braid-groups-free-rank-formula
  - gal-configuration-space-euler-characteristic-formula
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part3.md
---

1. **Free groups.** `Σ^m(ℤ) = S⁰`; `Σ¹(F_r) = ∅` for `r ≥ 2`, since kernels
   of nonzero characters are nontrivial normal subgroups of infinite index,
   which are not finitely generated.
2. **`n = 2`.** `B_2T` is free, and by Gal's formula
   `rank = 1 − e(UConf_2T) = Σ_v C(deg v − 1, 2)` (artifact part 3, §2).
   Rank 1 iff exactly one vertex has degree 3 and all others have degree
   `≤ 2`.
3. **`n = 3`.** `B_3T` is free. A non-arc tree contains a subdivided triod
   `Y`, and `UD_3Y ⊆ UD_3T` is a full, locally convex subcomplex, hence
   `π_1`-injective. `B_3Y ≅ F_3` by the radial rank formula. So `B_3T` has
   rank `≥ 2`.
4. **Radial trees.** The generating function is `(1 + (1−d)t)(1 − t)^{−d}`,
   so `e_n = C(n+d−2, d−1)(d − 1 − n(d−2))/n`. This is zero iff
   `(d,n) = (3,2)` and negative otherwise for `n ≥ 2`, `d ≥ 3`. The rank is
   `1 − e_n`.

Artifact part 3, §3.
