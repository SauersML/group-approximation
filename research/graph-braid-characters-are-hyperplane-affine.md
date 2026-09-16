---
rg: 2
id: graph-braid-characters-are-hyperplane-affine
kind: claim
title: "Every character of a graph braid group is induced by a function on the hyperplane classes of UD_n Gamma"
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part2.md
refuted_by:
  - two-strand-k4-and-theta-braid-characters-not-affine
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
- 2026-09-16 (swarm-zaremsky-1-08): false, and it fails for every
  subdivision of `K_4` at `n = 2`. When every `Γ − ē` is connected, affine
  classes factor through `H^1(Γ)`, so their dimension is at most `β_1 = 3`,
  while `b_1(UD_2K_4) ≥ 1 − e = 4`. The same holds for `Θ_3` with arcs of
  length at least 2 (`2 < 3`). See
  `two-strand-k4-and-theta-braid-characters-not-affine` and
  `research/artifacts/graph-braid-hyperplane-affine-counterexample-2026-09-16.md`.
