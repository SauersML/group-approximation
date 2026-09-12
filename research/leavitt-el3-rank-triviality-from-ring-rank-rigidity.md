---
rg: 2
id: leavitt-el3-rank-triviality-from-ring-rank-rigidity
kind: route
title: The class statement on ring rank rigidity specializes to the Leavitt instance
target: leavitt-el3-rank-models-over-finite-fields-are-trivial
requires:
  - el3-rank-models-factor-through-ring-rank-models
artifacts:
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

## Why sufficient

- `R = L_K(1,n)` with `K` finite of characteristic `p` and `n >= 2` is a simple algebra of
  characteristic `p` (Leavitt; Abrams--Aranda Pino).
- `R` has no unital ring homomorphism `C` into a rank ultraproduct `M`:
  - `t_0 s_0 = 1` gives `C(t_0) C(s_0) = 1`;
  - `M` is directly finite, so `C(s_0) C(t_0) = 1` and `C(1 - s_0 t_0) = 0`;
  - `1 - s_0 t_0 != 0`, since `(1 - s_0 t_0) s_1 = s_1`, so simplicity makes `C` zero, which
    contradicts `C(1) = 1`.
- So `R` meets the hypothesis of `el3-rank-models-factor-through-ring-rank-models`, which then
  makes every characteristic-`p` rank model of `EL_3(R)` trivial.
