---
rg: 2
id: generic-leavitt-full-mf-radical-via-full-idempotent
kind: route
title: A binary Leavitt family contains a full complementary idempotent
target: generic-leavitt-self-compression-full-mf-radical
requires:
  - full-complementary-idempotent-elementary-full-mf-radical
artifacts:
  - research/artifacts/full-complementary-idempotent-check-2026-09-05.md
---

## Why sufficient

With `s = s_0`, `t = t_0` one has `1 - s_0 t_0 = s_1 t_1` and
`t_1 (s_1 t_1) s_1 = 1`, so the ring hypothesis of
[[full-complementary-idempotent-elementary-full-mf-radical]] holds, and its
conclusion `Rad_MF(E_n(R)) = E_n(R)` for all `n ≥ 4` contains the target's
`n ≥ 16`.  The target's two Kazhdan hypotheses are not needed: the criterion
supplies them from Ershov--Jaikin-Zapirain on finitely generated subrings.
This is a genuine reduction, not a restatement, since the prerequisite drops
the second Leavitt branch and twelve of the sixteen coordinates.
