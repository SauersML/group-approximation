---
rg: 2
id: subshift-el-rank-lengths-force-non-uniform-simplicity
kind: claim
title: Each invariant measure of X gives the conjugation-invariant rank length rk_μ(g − 1) on EL_3(LC(X,F_2)⋊Z), so these simple Kazhdan groups are not uniformly simple
distinct_from:
  subshift-elementary-groups-are-character-rigid: that shows the unitary characters are only 1 and δ_e; this shows the rank lengths from invariant measures form a simplex of bi-invariant length functions that bound normal generation below.
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md
  - research/artifacts/sk-verify-14-2026-09-13-part7.md
---

**Statement.** Let `(X,T)` be a minimal homeomorphism of an infinite Cantor set, `R = LC(X,F_2) ⋊_T Z` and `G = EL_3(R)`. For an ergodic `μ ∈ M_T(X)` let `rk_μ` be the faithful Sylvester matrix rank function with `rk_μ(χ_U) = μ(U)`. Put `ℓ_μ(g) = rk_μ(g − I_3)`.
1. `ℓ_μ : G → [0,3]` is conjugation-invariant, symmetric, subadditive and faithful.
2. `ℓ_μ(e_ij(r)) = rk_μ(r)`, so `ℓ_μ(e_12(χ_U)) = μ(U)` and `μ ↦ ℓ_μ` is injective.
3. If `h` is a product of `N` conjugates of `g^{±1}`, then `ℓ_μ(h) ≤ N ℓ_μ(g)`.
4. For an infinite minimal subshift `X`, `G` is simple but not uniformly simple: writing `e_12(1)` as a product of conjugates of `e_12(χ_V)` needs at least `1/inf_μ μ(V)` factors, which is unbounded as `V` shrinks.

Contrast: every extreme character of `G` is `1` or `δ_e`, but its rank lengths carry the whole simplex of invariant measures.

**Status: established** by `subshift-el-rank-lengths-force-non-uniform-simplicity-proof`. UNREVIEWED; queued with sk-verify-13.

**Review (sk-verify-14, 2026-09-13): PASS.** Re-derived:
- invariance, symmetry, subadditivity and faithfulness of `ℓ_μ` on `M_3(R)` (a nonzero entry bounds the rank below);
- `ℓ_μ(e_ij(r)) = rk_μ(r)`;
- the lower bound on normal generation;
- non-uniform simplicity, with the extrema attained at ergodic measures.

See `research/artifacts/sk-verify-14-2026-09-13-part7.md` §4.
