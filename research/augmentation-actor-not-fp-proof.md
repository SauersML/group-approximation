---
rg: 2
id: augmentation-actor-not-fp-proof
kind: route
title: Compare the even lamp subgroup with the restricted wreath product
target: augmentation-actor-semidir-is-not-fp
requires:
  - simple-t-augmentation-module-is-aperiodic
---

The augmentation map `F_2^(A)->F_2` is `A`-invariant and has kernel `I_A`,
so it extends to a quotient `W->C_2` with kernel `Gamma_0`.  This proves the
index-two assertion.  Apply the standard theorem that a restricted wreath
product of a nontrivial finite group by an infinite group is not finitely
presented, followed by finite-index invariance of finite presentability.
