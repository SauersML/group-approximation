---
rg: 2
id: binary-leavitt-algebra-not-directly-finite-proof
kind: route
title: Square the second half of the relations against characteristic two
target: binary-leavitt-algebra-not-directly-finite
requires: []
artifacts:
  - GroupApproximation/Leavitt/Leavitt.lean
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

## Direct proof

`t_0 s_0 = 1` is one of the defining relations (`LeavittFamily.t0_s0`).

For the inequality, suppose `s_0 t_0 = 1`.  The idempotent relation
`s_0t_0 + s_1t_1 = 1` then gives `s_1 t_1 = 0` in characteristic two, so

    1 = (t_1 s_1)(t_1 s_1) = t_1 (s_1 t_1) s_1 = 0,

which is false in a nontrivial ring.  Nontriviality of `L_(F_2)(1,2)` is
available from simplicity together with `1 != 0`
(`LeavittSimplicity.exists_mul_mul_eq_one` is stated for nonzero `x`).

Nothing here is specific to `F_2`.  Over any coefficient field `s_0t_0 = 1`
forces `s_1t_1 = 1 - 1 = 0` by the same relation, and the squaring step is
characteristic-free.  `F_2` is fixed here only because it is the coefficient
field of the group in `openai-leavitt-unit-nonsofic`.
