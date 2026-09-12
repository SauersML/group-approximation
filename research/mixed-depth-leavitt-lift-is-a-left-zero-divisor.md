---
rg: 2
id: mixed-depth-leavitt-lift-is-a-left-zero-divisor
kind: claim
title: The natural mixed-depth lift of the Leavitt isometry is a left zero divisor, so its partial-symmetry defect cannot be removed
distinct_from:
  natural-leavitt-pair-lifts-have-partial-symmetry-defect: that computes tau sigma = 1 + D and the corrected tau'' sigma = 1 - e'; this shows sigma e' = 0, so sigma has no left inverse in any overring and e' is not in S_- sigma.
artifacts:
  - research/artifacts/crossed-product-zero-divisor-filters-2026-09-12.md
---

Work in `B = C(M_-, F_3) x| V ⊆ S_-` with the data of
`natural-leavitt-pair-lifts-have-partial-symmetry-defect`: Thompson units `g_0, g_1` with
`g_0(0x) = 00x` and `g_1(1x) = 01x`, the lifts `sigma = [g_0]P_0 + [g_1]P_1` and
`tau = [g_0^-1]P_00 + [g_1^-1]P_01`, the kernel idempotent `F`, the partial symmetry `D`, and
`e' = 2(F - D)`.

For every choice of `g_0, g_1`:
- `sigma F = sigma D = [g_1]1_(W_1) + [g_0]1_(W_2)`, so `sigma e' = 0`;
- `tau = sigma*` and `e'* = e'` under `[g] -> [g^-1]`, so `e' tau = 0`;
- `e' != 0`. So `e'` is not in `S_- sigma`, `sigma` is not left invertible in any ring containing `B`,
  and `tau` is not right invertible in any such ring;
- no `2 x 2` Gram matrix `[tau_i sigma_j]` over any ring containing `B` is invertible when some
  `sigma_j = sigma` or some `tau_i = tau`, whatever the other entries are.

This answers the open step recorded on `ternary-anti-central-summand-has-cohn-family` ("a witness needs
some `x` with `x sigma = e'`"): no such `x` exists. The defect is annihilated, not removable. The whole
skeleton built on the natural lifts is dead, including every completion by lifts of `s_1`.

**ESTABLISHED 2026-09-12** by `mixed-depth-leavitt-lift-left-zero-divisor-proof`. Verification requested
from w3-vf-linear.
