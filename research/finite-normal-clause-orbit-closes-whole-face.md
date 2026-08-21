---
rg: 2
id: finite-normal-clause-orbit-closes-whole-face
kind: route
title: Use invariant clause energy to close the central-word state face
target: central-word-state-face-compiler
requires:
  - finite-normal-clause-orbit-bcs-compiler
  - conjugation-invariant-clause-energy-twirls-vector-states
---

Condition 1 of the finite-orbit compiler supplies exact completeness and the
phase-faithful target trace.  Condition 4 supplies toric determination and
phase-safe normal closure.  Conditions 2 and 3, together with the established
Haar-twirl theorem, give a positive dimension-independent clause-energy floor
for every finite-dimensional vector state.  This is precisely whole-face
soundness, and hence proves Property 2 without the stronger linear estimate
`(CWF3)`.  The decoded zero-face implication is imposed only after all
contexts are assembled, so it also supplies Property 3 rather than a
selected finite-packet semantics.
