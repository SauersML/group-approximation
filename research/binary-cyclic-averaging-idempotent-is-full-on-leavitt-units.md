---
rg: 2
id: binary-cyclic-averaging-idempotent-is-full-on-leavitt-units
kind: claim
title: The averaging idempotent of a ternary permutation unit is full in the binary Leavitt unit group algebra
distinct_from:
  leavitt-visible-cyclic-corner-is-full-on-some-host: that is the twisted corner on the visible factor of some host; this is the untwisted corner 1 + g + g² in F_2[R^x] itself, which ascends to the host (4, 2, 3) but is not known to follow from it.
  thompson-v-order-three-averaging-idempotent-is-full: that is an order-three prefix-code element of Thompson's V; this is the permutation unit of a ternary Leavitt family in R^x, whose averaging idempotent has image equivalent to 1 in R.
artifacts:
  - research/artifacts/quaternary-twisted-corner-census-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)` with the ternary family `s_1 = s0`, `s_2 = s1 s0`, `s_3 = s1 s1`
(and `t_1 = t0`, `t_2 = t0 t1`, `t_3 = t1 t1`), let `g = s_2 t_1 + s_3 t_2 + s_1 t_3`, and
`e = 1 + [g] + [g²]` in `F_2[R^x]`. Exhibit `b, c` in `F_2[R^x]` with `c e b = 1`.

**What it gives.**
- `c e` and `e b` form a strict one-sided pair, so `F_2[R^x]` is not directly finite and `R^x` is not
  surjunctive (route `binary-cyclic-corner-fullness-gives-kaplansky-failure`).
- Multiplying by the visible scalar idempotent of `F_4[L_(F_4)(1,2)^x]` gives a solution of the twisted
  corner at `(q, d, m) = (4, 2, 3)` (route `binary-cyclic-corner-ascends-to-quaternary-twisted-corner`).

## Attempts

- **The image equation holds.** `b = s_1 + s_2 + s_3` and `c = t_1 + t_2 + t_3` give `c pi(e) b = 1` in
  `R`. Direct finiteness does not pass back from quotients, so the lift is the problem.
- **The augmentation does not obstruct.** `epsilon(e) = 1 = epsilon(1)`, so `F_2[R^x]` keeps its
  augmentation state and fullness asks only for a complement class of augmentation zero.
- **What does obstruct, if it exists.** Through the ascent to `(4, 2, 3)`, any state on the visible factor
  over `F_4`, or any characteristic-two rank model of a subgroup containing the scalars `F_4^x`, `g`,
  `δ = ω s_1 t_1 + ω² s_2 t_2 + s_3 t_3` and the witness supports with nonzero visible scalar component,
  kills this corner (`twisted-rank-models-kill-visible-cyclic-corner-witnesses`). No such state or model
  is known.
