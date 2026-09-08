---
rg: 2
id: order-two-low-rank-from-universal-ring
kind: route
title: Transport marked collapse from the universal ring through its defining ring maps
target: order-two-defect-rings-non-mf-at-ranks-two-and-three
requires:
  - order-two-universal-non-mf-at-ranks-two-and-three
  - order-two-defect-question-reduces-to-one-universal-ring
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

## Why sufficient

Fix `n in {2,3}`.  The first prerequisite is statement 2 of the second
prerequisite's equivalence at that `n`.  The equivalence upgrades it to
statement 3, marked collapse of `w = e_12(Q)` in `EL_n(A_2)`, and then to
statement 1, the class assertion.

Concretely, for any `R,s,t` satisfying `(OTC1)` the defining relations
give a unital ring map `A_2 -> R` and hence
`psi : EL_n(A_2) -> EL_n(R)` with `psi(w) = e_12(1-st)`.  Composing any
MF-target homomorphism out of `EL_n(R)` with `psi` kills `w`, hence kills
`e_12(1-st)`, which is nonidentity because `1 - st != 0`.  So no
MF-target homomorphism out of `EL_n(R)` is injective.

This is the whole payoff of the reduction: one analytic fact about one
explicit countable ring would decide the entire class at the two ranks
that the rank-four transport theorem leaves open.
