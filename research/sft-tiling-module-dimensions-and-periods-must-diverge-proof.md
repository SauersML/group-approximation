---
rg: 2
id: sft-tiling-module-dimensions-and-periods-must-diverge-proof
kind: route
title: A small torus forces commutation and a periodic legal configuration; bounded dimensions give a measure with a bounded-denominator small positive cylinder
target: sft-tiling-module-dimensions-and-periods-must-diverge
requires: []
artifacts:
  - research/artifacts/un-labbe-ring-torus-tilings-2026-09-13.md
---

Artifact §3, Theorem 2. It uses only the definitions of (Q1)–(Q3).

**Periods.**
- If `Z^2/Λ` has sup-diameter `<= 2D`, every difference of classes has a representative in `B_(2D)`. So
  periodicity and (Q2) make all `E_a(z)` commute.
- Commuting idempotents on a finite-dimensional space have a common eigenvector `v != 0`. Put `x(z)` = the tile
  with `E_(x(z))(z) v = v`.
- By (Q3) each `x|_(z + B_D)` lies in `L_(B_D)(Ω)`. Since `r <= D`, `x ∈ Ω`.
- `x` is `Λ`-periodic, but an infinite minimal system has no finite orbit.

**Dimensions.**
- For `ρ : B_m -> A` with `m <= D_j`, put `w_j(ρ) = rank(prod_h E_(ρ(h))(h)) / dim V_j`. Then:
  - `w_j(ρ) ∈ (1/dim V_j) Z_(>=0)`;
  - `w_j` has total mass 1 and consistent marginals, by (Q1) and commutation inside `B_(D_j)`;
  - `w_j` is translation-invariant, because conjugation by `U^z` preserves rank;
  - `w_j` vanishes off the language: every extension to `B_(D_j)` is killed by (Q3), and those extensions sum to the
    product for `ρ`.
- Suppose `dim V_j <= N` along a subsequence. A diagonal subsequence converges on all `ρ`. By Kolmogorov extension
  the limit is a shift-invariant probability measure `μ` on `Ω`.
- `μ` has full support by minimality, and no atoms, since there is no finite orbit. So some `ρ ∈ L(Ω)` has
  `0 < μ([ρ]) < 1/N`.
- Then `0 < w_j(ρ) < 1/N` eventually, which is impossible with denominator `<= N`.
