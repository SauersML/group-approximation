---
rg: 2
id: short-decoder-and-unpadded-cylinder-recursion
kind: route
title: Verify five coefficient words at the two idempotent values and solve the unequal-child cylinder recurrence
target: binary-cylinder-words-have-a-256-quadratic-bound
requires:
  - binary-subshift-language-has-quadratic-group-witnesses
  - unit-idempotent-elementary-group-has-three-torsion-generators
artifacts:
  - research/artifacts/pestov91-short-involution-mf-implications-2026-09-13.md
  - research/artifacts/find-pestov91-short-decoder-2026-09-13.py
---

Sections 1--2 give the words and recurrence proof. Evaluation at
`p=0,1` certifies the identities in the universal idempotent coefficient
algebra, even when the idempotent is noncentral in the larger ring.
The monomial product `s_23 w (s_13 s_23) w s_13` has length 44 and
equals `diag(u,u,u^{-2})`. Split each cylinder word into floor/ceiling
halves and use the spare-index commutator. The resulting recurrence
is bounded by `167n^2-100n-49`, with explicit nonnegative even/odd
induction slack as printed in section 2.
