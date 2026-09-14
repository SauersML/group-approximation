---
rg: 2
id: ghb7-kernel-stability-via-ghb7-stability
kind: route
title: Descend flexible HS stability from GHB_2(7) to its congruence kernel
target: ghb7-congruence-kernel-flexibly-hs-stable
requires:
  - ghb7-flexibly-hs-stable
  - cckw-ghb2-kms-group-structure
  - ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2
  - flexible-hs-stability-descends-to-retracts-finite-index
---

Let `G = G_{HB_2}(7)` and let `H = Ker(ψ)` be its congruence kernel.

1. **`G` is a finitely generated Kazhdan group.** It has three generators, and property (T) is
   item 1 of `cckw-ghb2-kms-group-structure` (also compiled as `hasKazhdanPropertyT_ghb7`).
2. **`H` has finite index in `G`.** This is the first item of
   `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`.
3. **Descent.** Assume `G` is flexibly HS stable (`ghb7-flexibly-hs-stable`). Item 2 of
   `flexible-hs-stability-descends-to-retracts-finite-index` then makes `H` flexibly HS stable, in
   Dogon's normalization: `D_n ≥ d_n`, `D_n/d_n → 1`, compressions `P_n π_n(h) P_n*`.
4. **Matching the target's notion.** The target `ghb7-congruence-kernel-flexibly-hs-stable` uses the
   Dogon--Vigdorovich notion, which asks only for `D_n ≥ d_n`. Dogon's notion satisfies it, so
   step 3 proves the target.

The only open input is `ghb7-flexibly-hs-stable`. Unlike the target, it concerns a triangle of
finite groups, and `triangle-of-finite-groups-hs-stability-is-edge-matching` restates it with no
infinite group in the data.
