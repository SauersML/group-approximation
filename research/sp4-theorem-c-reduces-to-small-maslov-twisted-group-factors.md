---
rg: 2
id: sp4-theorem-c-reduces-to-small-maslov-twisted-group-factors
kind: route
title: Combine Jiang's constant-cocycle injection with the twisted Bernoulli CE equivalence
target: sp4-isw-theorem-c-embeddable-twist-data-exists
requires:
  - sp4-maslov-circle-survives-in-bernoulli-l0-cohomology
  - scalar-twisted-bernoulli-ce-iff-twisted-group-factor-ce
  - sp4-small-maslov-twisted-group-factors-are-ce
---

Use the Bernoulli action of `Sp_4(Z)` on `T^Gamma`.  The first prerequisite
gives constant scalar Maslov cocycles converging pointwise to one and
remaining nontrivial in measurable Bernoulli cohomology.  The third chooses
them so their twisted group factors are Connes embeddable.  The second then
promotes each twisted group-factor embedding to a Connes embedding of the
corresponding twisted Bernoulli crossed product.  These are exactly the
three hypotheses of the target ISW Theorem-C packet.

