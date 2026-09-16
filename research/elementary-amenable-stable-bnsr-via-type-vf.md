---
rg: 2
id: elementary-amenable-stable-bnsr-via-type-vf
kind: route
title: "An elementary amenable F_infinity group is virtually of type F, hence virtually of finite cohomological dimension"
target: elementary-amenable-f-infinity-groups-have-stable-bnsr
requires:
  - elementary-amenable-f-infinity-groups-are-type-vf
  - virtually-finite-cd-f-infinity-groups-have-stable-bnsr
---

Let `G` be elementary amenable of type `F_∞`.

1. By `elementary-amenable-f-infinity-groups-are-type-vf`, some `H ≤ G` of
   finite index has a finite `K(H,1)` complex `L`. Let `d = dim L`.
2. The universal cover `L̃` is contractible. `H` acts on it freely by deck
   transformations, permuting cells, with finitely many orbits.
   - The augmented cellular chain complex `0 → C_d(L̃) → ⋯ → C_0(L̃) → Z → 0`
     is exact.
   - Each `C_i(L̃)` is a free `ZH`-module with basis the cells of `L` in
     dimension `i`.
   - So `Z` has a free resolution of length `d` over `ZH`, and `cd H ≤ d < ∞`.
3. `G` is of type `F_∞`, and `H` is a finite-index subgroup of finite
   cohomological dimension. By
   `virtually-finite-cd-f-infinity-groups-have-stable-bnsr`,
   `Σ^m(G) = Σ^n(G)` for all `m ≥ n := max(cd H, 2)`. ∎
