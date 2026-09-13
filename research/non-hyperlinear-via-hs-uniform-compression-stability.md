---
rg: 2
id: non-hyperlinear-via-hs-uniform-compression-stability
kind: route
title: Uniform compression stability at the Kun--Thom pair makes every tracial model of the wreath kill its root-lamp defect
target: non-hyperlinear-group
requires: [hs-uniform-compression-stability-at-the-theorem-e-pair, kazhdan-commutant-compression-stability-is-finitary, kun-thom-wreath-carries-rigid-defect, rigid-compression-defect-normalization-dichotomy]
artifacts:
  - research/artifacts/unified-compression-rigidity-2026-09-12.md
---

1. `hs-uniform-compression-stability-at-the-theorem-e-pair` and
   `kazhdan-commutant-compression-stability-is-finitary` give: for every homomorphism
   `sigma : G -> U(prod_U M_n)`, the group `sigma(G)` normalizes `C(sigma(Gamma))`.
2. Put `W = (direct_sum_(G/Gamma) Z/2) x| G`. Suppose `rho : W -> U(prod_U M_n)` is injective.
3. Apply step 1 to `sigma = rho|G`, as in the first half of the proof of
   `rigid-compression-defect-normalization-dichotomy`. The root lamp `e_Gamma` centralizes
   `Gamma`, so `rho(e_Gamma) in C(sigma(Gamma))`. So `rho(t e_Gamma t^-1)` commutes with
   `rho(gamma)` for all `gamma in Gamma`.
4. `kun-thom-wreath-carries-rigid-defect` gives a strict compressor `t` and
   `gamma in Gamma \ t Gamma t^-1` with `[t e_Gamma t^-1, gamma] != 1` in `W`.
5. Steps 3 and 4 contradict injectivity. So `W` is not hyperlinear.

`W` is finitely generated, so this establishes `non-hyperlinear-group` once the first
requirement holds. No trace condition is used anywhere.
