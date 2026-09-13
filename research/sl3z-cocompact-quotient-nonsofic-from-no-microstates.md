---
rg: 2
id: sl3z-cocompact-quotient-nonsofic-from-no-microstates
kind: route
title: Absence of topological microstates for SL3(Z) on SL3(R)/Λ makes the action nonsofic
target: sl3z-on-cocompact-lattice-quotient-is-not-sofic
requires:
  - sl3z-cocompact-quotient-admits-no-topological-microstates
  - uniquely-ergodic-action-sofic-iff-topological-microstates
---

Conditional route. Let `Λ`, `F` and `ε` be as in `sl3z-cocompact-quotient-admits-no-topological-microstates`.
`SL_3(Z)` is sofic, and it acts on the compact metric space `SL_3(R)/Λ` by homeomorphisms preserving
Haar measure. If `SL_3(Z) ↷ SL_3(R)/Λ` were sofic, part 1 of
`uniquely-ergodic-action-sofic-iff-topological-microstates` would give an `(F,ε)`-microstate. So the
action is not sofic.

Part 1 does not use unique ergodicity. The converse, that nonsoficity implies the absence of
microstates, is part 2 together with `sl3z-cocompact-quotient-uniquely-ergodic-minimal`.
