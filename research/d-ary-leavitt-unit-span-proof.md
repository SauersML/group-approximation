---
rg: 2
id: d-ary-leavitt-unit-span-proof
kind: route
title: Off-diagonal corners are square-zero, diagonal corners are products of two of them, and the corners rebuild the element
target: leavitt-units-span-every-d-ary-leavitt-algebra
requires: []
artifacts:
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

This is the four-step argument of `leavitt-unit-span-surjection-proof`, with the indices widened
from `{0, 1}` to `{1, ..., d}`. Write `U` for the additive span of the units.

1. **Square-zero elements.** If `x^2 = 0`, then `1 + x` is a unit with inverse `1 - x`, so
   `x = (1 + x) - 1` lies in `U`.
2. **Products of two square-zero elements.** If `x^2 = y^2 = 0`, then
   `xy = (1 + x)(1 + y) - 1 - x - y` lies in `U`.
3. **Every corner.** For `i != j` and any `a`, `(s_i a t_j)^2 = s_i a (t_j s_i) a t_j = 0`. For each
   `i` pick `j != i`, which exists because `d >= 2`. Then `t_j s_j = 1` gives
   `s_i a t_i = (s_i a t_j)(s_j t_i)`, a product of two square-zero elements.
4. **Reassembly.** `a = (sum_i s_i t_i) a (sum_k s_k t_k) = sum_(i,k) s_i (t_i a s_k) t_k`, a finite
   sum of corners, so `a` lies in `U`.

Over `F_q`, scalar multiples of units are units, so `U` is an `F_q`-subspace, and the evaluation of the
group algebra is onto.
