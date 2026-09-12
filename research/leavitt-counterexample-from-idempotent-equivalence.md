---
rg: 2
id: leavitt-counterexample-from-idempotent-equivalence
kind: route
title: Apply the strict idempotent-compression criterion to e and f
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - leavitt-e-f-murray-von-neumann-equivalence
  - strict-idempotent-equivalence-breaks-direct-finiteness
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

The first prerequisite supplies a strict equivalence `e~f` with `f<e` inside
`S`.  The second says that any unital ring containing such a pair of
idempotents is not directly finite: pad the implementing elements by `1-e`.
Applying it to `S=F_2[L_(F_2)(1,2)^x]` gives the target.
