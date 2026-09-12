---
rg: 2
id: ultrapower-comparison-rank-density-division-proof
kind: route
title: Select a near projection of one n-th the profile, then peel equivalent copies off the projection by comparison
target: ultrapower-comparison-with-rank-density-divides-projections
requires: []
artifacts:
  - research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md
---

Section 3 of the artifact.

1. **Represent.** Represent `p` by positive contractions `p_m ∈ M_k(A)` whose
   defect tends to `0`.
2. **Select.** RD_b gives near projections `b_m ∈ M_k(A)` with
   `|τ(b_m) − τ(p_m)/n| < 1/m` and defect below `1/m`. So `e' = [(b_m)]` is a
   projection with `σ(e') = σ(p)/n` for every limit trace.
3. **Peel.** For `j < n − 1`, the projection `p − (e_1 + … + e_j)` has profile at
   least `σ(e')`. Comparison gives `e_{j+1}` under it, equivalent to `e'`.
4. **Remainder.** It has profile `σ(e')`. Comparison gives `w` with `w*w = e'`
   and `ww*` under it. The difference is a positive element vanishing on every
   limit trace, hence zero. So the remainder is equivalent to `e'`.
5. **Assemble.** With `w_i*w_i = e'` and `w_i w_i* = e_i`, the elements
   `E_ij = w_i w_j*` are matrix units of a unital `M_n ⊂ p M_k(A^U) p`.
