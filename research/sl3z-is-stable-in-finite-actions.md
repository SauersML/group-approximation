---
rg: 2
id: sl3z-is-stable-in-finite-actions
kind: claim
title: SL3(Z) is stable in finite actions
distinct_from:
  alekseev-thom-stability-finite-actions-boundary: that records the literature boundary for stability in finite actions of general residually finite groups; this is the named statement for SL3(Z)
  sln-z-flexibly-hs-stable: that is flexible Hilbert-Schmidt stability in unitary matrices; this is the permutation notion that asks only for weak containment of limit actions in finite actions
---

**OPEN.** For every sofic approximation `σ_k : SL_3(Z) → Sym(V_k)`, the p.m.p. action of `SL_3(Z)` on the
Loeb ultraproduct of the `V_k` is weakly contained in the family of finite `SL_3(Z)`-actions.
This is stability in finite actions, as used in `stable-finite-actions-blocks-codense-kazhdan-coset-soficity`
and in `alekseev-thom-stability-finite-actions-boundary`.

It is strictly weaker than flexible P-stability. No Hamming correction is asked for, only reproduction
of partition statistics by genuine finite actions.

## Attempts

* **Becker--Lubotzky instability.** Their theorem refutes strict P-stability for infinite sofic Kazhdan
  groups via punctured finite actions. These are flexibly repairable, so they say nothing about this
  weaker property (recalled as in `sl3-prime-stable-finite-actions-excludes-coset-soficity`).
* **Alekseev--Thom quotient inheritance.** Their Theorem A(ii) passes stability in finite actions to
  quotients by Kazhdan normal subgroups. It gives no input for `SL_3(Z)` itself. It is open whether any
  residually finite group fails the property.
* **A test action.** `SL_3(Z) ↷ SL_3(R)/Λ`, for `Λ` from a cubic division algebra, is free, mixing and
  uniquely ergodic. If it is sofic, it is the factor of a limit action of a sofic approximation. So if
  it is sofic but not weakly contained in finite actions, this claim fails
  (`sl3z-cocompact-nonsofic-from-stability-and-no-finite-approx`). No proof of either input is
  known.
