---
rg: 2
id: sl2-root-kazhdan-untwisted-first-level-moments-proof
kind: route
title: Two M4RI ranks of the coset-indicator matrix of SL_2(64) give the first-level homology and moments of the untwisted q = 8 member
target: sl2-root-kazhdan-untwisted-first-level-moments
requires: [edge-twist-moment-test-elementary-abelian-edges, sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2]
artifacts: [experiments/sl2-root-triangle-kazhdan/moment2.py, experiments/sl2-root-triangle-kazhdan/run4.out, experiments/sl2-root-triangle-kazhdan/run3.out]
---

**Complex.** `ρ` is injective on the vertex groups and `N = ker ρ` acts freely on the development `X`
(`sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2`).
- **Cells.** The cells of `N\X` are the cosets of the stabilizers in `Q = SL_2(64)`. There are
  `2·|Q|/|SL_2(8)| + |Q|/|Q| = 1041` vertices, `3|Q|/8 = 98,280` edges (right cosets `E_e g`) and
  `|Q| = 262,080` triangles.
- **Boundary.** Triangle `g` has edges `E_12 g`, `E_13 g`, `E_23 g`, so `∂_2` is the coset-indicator
  matrix `B` (edges × triangles).
- **Homology.** `X` is contractible, so `H_*(N;F_2) = H_*(N\X;F_2)`. There are no 3-cells, so
  `b_2 = |Q| - rank B`. Then `b_1 = b_0 + b_2 - χ` with `b_0 = 1`.

**Moments.** By `edge-twist-moment-test-elementary-abelian-edges` (computation form),
`dim I_N = rank [B; R] - rank B`.
- `R` has one row for each edge type `e` and each bit `j` of the integer encoding of `F_64`, `0 <= j < 6`.
- The row is `g ↦ bit_j(x)`, where `g = x·q_0(E_e g)`, `q_0` is the minimal-index element of the coset
  `E_e g`, and `x ∈ F_8` is the parameter of the involution carrying `g` to `q_0`.
- The six bit functionals restricted to `F_8` span `Hom(F_8, F_2)`, so the rows span the three moment
  functionals of every twist.

**Script checks.**
- `SL_2(64)` is enumerated and has `N(N^2-1)` elements.
- Every product `x·g` lies in `SL_2(64)`.
- Each edge type has exactly `|Q|/8` cosets.
- Ranks are exact `F_2` ranks by M4RI.

**Output** (`run4.out`): `rank B = 97,222`, `rank [B;R] = 97,231`, `χ = 164,841`, `b_2 = 164,858`,
`b_1 = 18`, `dim I_N = 9`.

**Independent calibration.**
- For the untwisted `q = 4` member, the script gives `b_1 = 20` (`run4.out`).
- `untw.g` builds the same group from vertex-group presentations and computes `H_1` of the kernel by
  Reidemeister–Schreier in GAP. It returns `(Z/2)^11 × (Z/4)^9` (`run3.out`), whose mod-2 rank is `20`.

The two code paths share no code. ∎
