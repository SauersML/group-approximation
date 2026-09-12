---
rg: 2
id: swap-separated-support-no-go-proof
kind: route
title: Evaluate a supported solution in a finite-dimensional sign representation of its support group
target: swap-separated-pairs-avoid-finitely-represented-supports
requires:
  - ternary-leavitt-swap-problem-splits-at-central-involution
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-swap-separated-pairs-2026-09-12.md
---

## Why sufficient

`ternary-leavitt-swap-problem-splits-at-central-involution` defines `eps_- = 2(1 - [z])` and
`e_- = eps_- . 2(1 + [w])`.

* **Evaluation.** Extend `rho` linearly to `F_3[H]`. The equations lie in `F_3[H]`, since
  `z, w` are in `H`, and `rho(eps_-) = 2(1 - (-1)) = 1`.
* **Separated pairs.** In `M_n(k)`, `rho(c) rho(a) = 1` makes `rho(a)` invertible, so
  `rho(c) rho(w) rho(a) = 0` gives `rho(w) = 0`. That is impossible.
* **Corner solutions.** `rho(c) . 2(1 + rho(w)) . rho(b) = 1` needs `1 + rho(w)` invertible, which
  fails when `rho(w)` has eigenvalue `-1`.
* **Finite orbits.** The span of a finite orbit is a finite-dimensional representation, and
  `z = -1` acts as `-1` on every `R`-module.
* **Finite quotients.** Take the regular representation of the quotient, cut by
  `2(1 - zbar)`. It is nonzero when `zbar != 1`. When `wbar != 1` as well,
  `2(1 - zbar) . 2(1 - wbar) != 0`, so `w` has eigenvalue `-1` there.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 10 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
