---
rg: 2
id: localized-square-return-promotion-equivalence-proof
kind: route
title: Use the terminal localized norm obstruction and the vacuous cyclic-factor witness
target: localized-square-return-promotion-is-goal-equivalent
requires:
  - compressed-finite-order-wandering-is-terminal
  - nonhyperlinearity-has-a-finite-presentation-witness
  - nonhyperlinear-group-has-finite-canonical-microstate-witness
---

Forward, apply the terminal theorem to the fixed nonzero group-algebra
element `(w^2-1)q`.  Reverse, replace a nonhyperlinear group by its finitely
presented witness and take its direct product with `Z`; with `q=1` and `w`
the cyclic generator, the group has no full canonical microstate sequence,
so the universal localized-return assertion is vacuous.
