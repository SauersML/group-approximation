---
rg: 2
id: modular-nested-equivalence-refutes-leavitt-direct-finiteness
kind: route
target: leavitt-unit-group-algebra-not-directly-finite
title: Pad a properly nested equivalent pair by the complement of the larger idempotent
requires:
  - modular-nested-idempotents-equivalent-over-leavitt-units
artifacts:
  - research/artifacts/binary-kernel-nested-idempotents-2026-09-12.md
---

## Why sufficient

- **Normalize the pair.** Given `xy = e` and `yx = f` with `0 != f < e`, replace `x` by `exf`
  and `y` by `fye`. Both products are unchanged, so `x in eSf` and `y in fSe`.
- **Pad.** Put `A = (1 - e) + x` and `B = (1 - e) + y`. Since `(1 - e) f = 0 = f (1 - e)`, every
  cross term vanishes, so `AB = (1 - e) + e = 1` and `BA = (1 - e) + f = 1 - (e - f)`.
- **Conclude.** `e - f != 0`, so `BA != 1`. With `alpha = A` and `beta = B` this is the
  root's statement: `F_2[R^x]` is not directly finite.
