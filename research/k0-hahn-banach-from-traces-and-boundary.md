---
rg: 2
id: k0-hahn-banach-from-traces-and-boundary
kind: route
title: Boundary classes after stabilized unitization give the universal Hahn-Banach property (a restatement, not a reduction)
target: every-separable-nuclear-qd-algebra-has-k0-hahn-banach
requires: [k0-hahn-banach-for-boundary-singular-classes, stw07-trace-invisible-classes-carry-hahn-banach]
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

Given a separable nuclear quasidiagonal `A` and singular `x`, pass to
`E=(A tensor K)~`.  Its only trace is a character vanishing on `x`, so `x` is
a boundary class of an algebra whose traces are all quasidiagonal.  The
boundary claim kills `x` in `E`, and the transfer claim returns the kill to
`A`.

**Warning, recorded 2026-09-11.**  The boundary prerequisite is equivalent to
the target: the target trivially implies it.  This route therefore renames
the problem.  The earlier version of this route also required the exact X(1)
residual and the sign-change theorem.  Those prerequisites were redundant and
were removed when `stw07-trace-invisible-classes-carry-hahn-banach` was
proved.  The trace-sign theorems remain genuine results about classes some
trace detects, but they are not steps of this route.
