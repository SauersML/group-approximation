---
rg: 2
id: leavitt-inverse-defects-visible-or-invisible-proof
kind: route
title: Translate by the unit of the image pair, or by the image unit when the defect dies
target: leavitt-inverse-defects-are-visible-or-invisible
requires:
  - leavitt-one-sided-pairs-are-unit-translates-of-s0-t0
  - leavitt-unit-group-algebra-surjects-onto-leavitt
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

## Why sufficient

Section 4 of the artifact. `pi` is a unital ring map, so `pi(b) pi(a) = 1`.

* **Visible case.** If `pi(ab) != 1`, the orbit theorem gives `w` in `Q` with
  `w pi(a) = s_0` and `pi(b) w^(-1) = t_0`. The translated pair
  `([w] a, b [w^(-1)])` still multiplies to `1` one way, and the other product
  is a conjugate of `ab`, hence not `1`.
* **Invisible case.** If `pi(ab) = 1`, then `pi(a)` is a unit `r` of `R` and
  `([r^(-1)] a, b [r])` lies over `(1, 1)`.

**The converse.** A pair over `(s_0, t_0)` has `ab != 1`, because otherwise
`s_0` would be a unit of `R`. A failure inside the unital subring `K^+` is a
failure in `S`.

**Normalizing the partner.** For a lift `a` of `s_0` with `b a = 1`,
`pi(b) = t_0 + gamma t_1` with `gamma = pi(b) s_1`. The involution
`v = 1 + s_0 gamma t_1` in `Q` fixes `s_0` on the left and sends `pi(b)` to
`t_0` on the right.
