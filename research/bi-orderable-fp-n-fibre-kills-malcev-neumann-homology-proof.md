---
rg: 2
id: bi-orderable-fp-n-fibre-kills-malcev-neumann-homology-proof
kind: route
title: Series supported on the kernel, a twisted Laurent ring over them, finite-dimensional kernel homology is torsion and dies in the Ore localization
target: bi-orderable-fp-n-fibre-kills-malcev-neumann-homology
requires: []
artifacts:
  - research/artifacts/zp-raag-virtual-kernels-2026-09-13-part1.md
---

Complete proof in `research/artifacts/zp-raag-virtual-kernels-2026-09-13-part1.md`,
Section 2, steps (a)--(i). Inputs: the Malcev--Neumann theorem that `F((G, <))` is a division
ring for a bi-ordered group `G` (A. I. Malcev 1948, B. H. Neumann 1949), and the elementary
facts that a twisted Laurent polynomial ring over a division ring is a principal ideal
domain on both sides, hence an Ore domain, and that Ore localization is flat.

Outline: `D_K = F((K,<))` is a division subring; `t` with `ψ(t) = 1` normalizes it; the `t^j`
are independent over `D_K` (disjoint coset supports), so `R = D_K[t^{±1}; α] ⊆ D` and its
fraction field `Q` embeds in `D`; `R ⊗_{F[H]} P_* ≅ D_K ⊗_{F[K]} P_*`, whose homology
`H_i(K; D_K)` is finite-dimensional over `D_K` for `i ≤ n`, hence `R`-torsion, hence
`Q ⊗_R H_i = 0`; flatness gives `H_i(H; D) = D ⊗_Q Q ⊗_R H_i = 0`.
