---
rg: 2
id: stw07-singular-class-boundary-proof
kind: route
title: Goodearl-Handelman state extension from the order unit, then states are traces
target: stw07-singular-classes-change-sign-or-sit-on-boundary
requires: [blackadar-rordam-haagerup-k0-states-are-traces]
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

Artifact Section 4.  Stable finiteness makes `(K_0(A), K_0^+, [1])` a
partially ordered group with order unit.

By the Goodearl--Handelman state extension theorem, the state `ku -> k` on
`Zu` extends to states whose values at `x` fill an interval with lower end
`sup{k/m : ku <= mx}`.  If no `mx >= u` holds, that supremum is `<= 0`, so
some state is `<= 0` at `x`.

Singularity excludes `mx >= [1]`.  So if `x^ > 0` on every trace, then since
every state is a trace (the required claim), no state could be `<= 0` at `x`,
a contradiction.  Apply the same to `-x`.
