---
rg: 2
id: stw07-singular-classes-change-sign-or-sit-on-boundary
kind: claim
title: A singular K_0-class of a unital exact stably finite algebra is never strictly one-signed on traces
distinct_from:
  stw07-sign-changing-qd-trace-values-kill-class: that kills classes taking both signs on quasidiagonal traces; this shows that, over all traces, a singular class can only take both signs or vanish on a nonempty face.
  blackadar-rordam-haagerup-k0-states-are-traces: that identifies K_0-states with traces; this combines it with state extension to bound the sign pattern of a singular class.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**ESTABLISHED (Theorem C of the artifact).**  Let `A` be separable, unital,
exact and stably finite, and let `x in K_0(A)` satisfy
`Zx cap K_0^+(A) = {0}`.  Then `x^ = (Tr tensor tau)(x)` is neither strictly
positive nor strictly negative on the tracial state space `T(A)`.

Consequently, if every tracial state of a separable unital nuclear
quasidiagonal `A` is quasidiagonal, then by
`stw07-sign-changing-qd-trace-values-kill-class` every singular class of `A`
is killed by a faithful model unless it is a **boundary class**: `x^ >= 0` (or
`<= 0`) on `T(A)` with nonempty zero face.
