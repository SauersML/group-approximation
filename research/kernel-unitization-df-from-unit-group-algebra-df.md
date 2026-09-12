---
rg: 2
id: kernel-unitization-df-from-unit-group-algebra-df
kind: route
title: A directly finite Leavitt unit group algebra has a directly finite unitized evaluation kernel
target: leavitt-evaluation-kernel-unitization-directly-finite
requires:
  - leavitt-unit-group-algebra-is-directly-finite
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/leavitt-invisible-corner-transfer-2026-09-12.md
---

## Why sufficient

`K^+ = F_2 1 + ker pi` is a unital subring of `F_2[L_(F_2)(1,2)^x]` with the same
identity. A one-sided inverse pair in `K^+` is one in the group algebra, so direct
finiteness passes down to the subring.

## An intended cycle

This is the trivial half of an equivalence. The other half is the kernel-corner transfer
of `leavitt-kaplansky-failures-have-invisible-witnesses` (landed by `gk-l2-visible`):
direct finiteness of `K^+` gives direct finiteness of the group algebra. The cycle warning
between this route and that one is correct and informational. Neither completes without an
open claim, so nothing is established through the cycle.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 13 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
