---
rg: 2
id: local-steinberg-heisenberg-rank-blindness-proof
kind: route
title: Restrict the ambient regular representation to each idempotent root line
target: local-steinberg-heisenberg-packets-are-coefficient-rank-blind
requires: []
artifacts:
  - research/artifacts/fanizza-root-heisenberg-rank-blindness-2026-08-21.md
---

For every nonzero idempotent `e_r`, the scalar line `F_2e_r` is a copy of
`F_2`.  The Steinberg commutator formula therefore identifies the subgroup
in `(RHB2)` with `UT_3(F_2)`, independently of `r`.  Restricting a finite
group's left regular representation to any subgroup gives copies of the
subgroup regular representation, so all joint packet moments and
multiplicities are independent of `r`.

Equations `(RHB4)--(RHB5)` depend only on the two identities for the scalar
line and `e_r^2=e_r`, which also do not contain `r`.  Since `r/n` ranges from
`1/n` to `1`, the local packet data cannot determine coefficient rank or a
source-Gram projection.
