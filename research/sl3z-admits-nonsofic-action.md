---
rg: 2
id: sl3z-admits-nonsofic-action
kind: claim
title: SL3(Z) has a p.m.p. action that is not sofic
root: true
distinct_from:
  groups-containing-kun-thom-pair-have-nonsofic-actions: that gives nonsofic actions to every group containing an infranormal non-normal Kazhdan pair; no such pair is known inside SL3(Z), and this asks whether the arithmetic lattice itself leaves Paunescu's class
  kun-thom-free-nonsofic-action: that is a nonsofic action of a non-linear elementary group over Laurent polynomials; this asks the same for the standard higher-rank lattice
---

**OPEN.** `SL_3(Z)` admits a p.m.p. action on a standard probability space that is
not sofic (Păunescu Definition 1.4). Equivalently (Păunescu Theorem 3.1),
`SL_3(Z)` is not in Păunescu's class `𝒮`, and then it has a free nonsofic action.

Why ask. `SL_3(Z)` is residually finite and Kazhdan, the prototype of the groups
Kun--Thom's mechanism needs, yet the recorded counterexamples live on
`EL_r(F_q[x_1^(±1),...,x_d^(±1)]) ⋊ SL_d(Z)`. By
`sofic-action-class-closed-under-commensurability` the answer is the same for
every finite-index subgroup of `SL_3(Z)` and every group commensurable with it.

## Attempts

* **Kun--Thom Theorem C.** Needs a Kazhdan subgroup `Γ` that is infranormal but
  not normal. A finite-index infranormal subgroup is normal (its compressions have
  the same index, so the compression semigroup is the normalizer; argument in
  `kun-thom-free-nonsofic-action-proof`, Step 0). So the attack needs an
  infinite-index Kazhdan subgroup of `SL_3(Z)` whose compression semigroup
  generates `SL_3(Z)`. None is recorded here.
* **Overgroup transfer.** `groups-containing-kun-thom-pair-have-nonsofic-actions`
  would apply if `SL_3(Z)` contained an infranormal non-normal Kazhdan pair, or if
  some subgroup of it had a nonsofic action. Neither is known.
* **Mixing actions.** Blind to the fixed-algebra mechanism for every Kazhdan
  subgroup (`kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions`), so a
  mixing candidate such as a Gaussian or algebraic action needs a different
  obstruction.
