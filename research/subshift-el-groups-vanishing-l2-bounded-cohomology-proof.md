---
rg: 2
id: subshift-el-groups-vanishing-l2-bounded-cohomology-proof
kind: route
title: The cut stabilizer is an amenable normalish subgroup, so BKKO's propositions apply and (CS) fails
target: subshift-el-groups-vanishing-l2-betti-and-bounded-cohomology
requires:
  - cut-stabilizers-of-el-n-are-locally-finite-normalish
  - amenable-normalish-kills-l2-betti-bounded-cohomology
artifacts:
  - research/artifacts/sk-cstar-simple-2-2026-09-13-part1.md
---

**Items 1 and 2.** `H = S_y` is locally finite, hence amenable, and normalish (`cut-stabilizers-of-el-n-are-locally-finite-normalish`,
also modulo the centre). `amenable-normalish-kills-l2-betti-bounded-cohomology` gives both.

**Item 3.** This is the argument of BKKO l.945, written out.
- `G` is simple, infinite and Kazhdan, so it is non-amenable and its amenable radical is trivial. Over `F_q`, `EL_n/Z` is simple
  in the same way.
- (CS) requires, for the weakly regular representation `π = λ_{G/H}` (weakly regular because `H` is amenable), an
  SOT-neighbourhood `U` of `I` with `π^{-1}(U) ⊆ R_a(G) = {e}`.
- Every such `U` contains a basic set `{T : ‖(T−I)ξ_j‖ < ε, j ≤ k}`.
  - Approximate each `ξ_j` within `ε/3` by `η_j` supported on finitely many cosets `s_1H,…,s_pH`.
  - Every `g ∈ ⋂_i s_iHs_i^{-1}` fixes those cosets, so `‖(π(g)−I)ξ_j‖ ≤ 2‖ξ_j − η_j‖ < ε`.
  - That intersection is infinite, so `π^{-1}(U)` is infinite. Contradiction.

**Model check.**
- Linear groups have (CS) (BKKO). `G` is not linear: it is finitely generated, infinite and simple, so not residually finite,
  while f.g. linear groups are residually finite.
- Item 1 is consistent with property (T), which already forces `β_1^{(2)} = 0`.
