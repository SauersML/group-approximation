---
rg: 2
id: graph-braid-characters-are-hyperplane-affine
kind: claim
title: "Every character of a graph braid group is induced by a function on the hyperplane classes of UD_n Gamma"
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part2.md
---

For sufficiently subdivided `Γ`, the map from antisymmetric functions on
oriented hyperplane classes of `UD_nΓ` to `Hom(B_nΓ, ℝ) = H^1(UD_nΓ; ℝ)` is
surjective.

## Attempts

- 2026-09-13 (z1-08-graph-braid): every such function is a cocycle
  (artifact part 2, §1). What is missing is that every class has a
  hyperplane-constant representative. Plan: compare dimensions with the
  Ko–Park formula for `H_1(B_nΓ)` (arXiv:1101.2648), or show `UD_nΓ` is
  special in the Haglund–Wise sense, pull characters back along the local
  isometry to a Salvetti complex (Crisp–Wiest embed graph braid groups in
  RAAGs), and check that the restriction `H^1(RAAG) → H^1(B_nΓ)` is onto.
  That restriction step is where it can fail.
