---
rg: 2
id: mixed-depth-leavitt-lift-left-zero-divisor-proof
kind: route
title: Multiply the lift into the defect term by term in the odd-measure crossed product
target: mixed-depth-leavitt-lift-is-a-left-zero-divisor
requires:
  - signed-thompson-algebra-is-odd-measure-crossed-product
  - natural-leavitt-pair-lifts-have-partial-symmetry-defect
artifacts:
  - research/artifacts/crossed-product-zero-divisor-filters-2026-09-12.md
  - research/artifacts/gk-vf-linear-b-verification-2026-09-12.md
---

Proposition 1.1 of the artifact.
- `sigma F = [g_0]1_(W_2) + [g_1]1_(W_1)`, because `W_2 ⊆ U_0`, `W_1 ⊆ U_1` and `U_0 ∩ U_1 = ∅`.
- `sigma D` has four terms, computed with `1_U [k] = [k] 1_(k^-1 U)`:
  - `[g_0]P_0 [h]1_(W_1) = [g_1]1_(W_1)`, since `h^-1(0) = A` and `W_1 ⊆ U_A`;
  - `[g_1]P_1 [h^-1]1_(W_2) = [g_0]1_(W_2)`, since `h(1) = B'` and `W_2 ⊆ U_(B')`;
  - the two cross terms vanish, since total mass one forces `mu(h(0)) = 0` on `W_2` and
    `mu(h^-1(1)) = 0` on `W_1`.
- So `sigma (F - D) = 0`. Applying the anti-automorphism `[g] -> [g^-1]`, with `sigma* = tau`
  and `D* = D`, gives `e' tau = 0`.
- `e' != 0` because its identity grade is `2F`. A left inverse `z` of `sigma` would give
  `e' = z sigma e' = 0`.
- A Gram matrix `T Sigma` with an inverse `N` makes `Sigma` left invertible. But `Sigma` kills the column
  carrying `e'` in the slot of `sigma`. Dually, the row carrying `e'` in the slot of `tau` kills `T`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 7 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *`sigma F`, and all four terms of `sigma D`, with both cross terms emptied by total mass;*
- *`*` fixes `C(M_-, F_3)` pointwise, `sigma* = tau` and `D* = D`;*
- *`e' != 0`, and the Gram-matrix argument for columns and for rows.*

*Scope: natural lifts only, for every `g_0, g_1`. The `s_1` remark cites an artifact section not yet on main and was not checked.*
