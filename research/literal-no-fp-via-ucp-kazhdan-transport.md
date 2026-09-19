---
rg: 2
id: literal-no-fp-via-ucp-kazhdan-transport
kind: route
title: The u.c.p. Kazhdan transport refutes amenability of the canonical trace
target: literal-group-lacks-factorization-property
requires: [ucp-hs-transport-kills-literal-mark]
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

If u.c.p. Hilbert--Schmidt models kill the mark, then along any amenable-trace
model `tr φₙ(u_w) → 1 ≠ 0 = τ_E(u_w)`, contradicting the trace clause.  So no
amenable-trace model exists and `E` lacks the factorization property (Brown,
Theorem 4.1.9).  One step, the same shape as the operator-norm refutation
already formalized in `NinetyNineProblems.ProblemX`.
