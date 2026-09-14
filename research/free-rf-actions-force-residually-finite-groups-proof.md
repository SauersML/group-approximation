---
rg: 2
id: free-rf-actions-force-residually-finite-groups-proof
kind: route
title: Direct proof that a free residually finite action forces a residually finite acting group
target: free-rf-actions-force-residually-finite-groups
requires: []
artifacts:
  - research/artifacts/sk-general-actions-b-converse-map-2026-09-13-part1.md
---

1. Let `g ≠ e`. By freeness and compactness, `δ = min_x d(gx, x) > 0`.
2. Residual finiteness with `F = {g}` and `ε = δ/2` gives a finite nonempty `E ⊆ X` and a genuine action `β : Γ -> Sym(E)` with `d(gz, β(g)z) < ε` for `z ∈ E`.
3. Then `d(β(g)z, z) >= d(gz, z) − d(gz, β(g)z) > δ/2 > 0`, so `β(g) ≠ id`.
4. So `ker β` is a finite-index normal subgroup that avoids `g`. As `g` was arbitrary, `Γ` is residually finite. ∎
