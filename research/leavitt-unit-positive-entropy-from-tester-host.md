---
rg: 2
id: leavitt-unit-positive-entropy-from-tester-host
kind: route
title: Pass a positive-entropy action of the tester host down to the Leavitt unit group
target: leavitt-unit-group-has-positive-rokhlin-entropy-action
requires:
  - tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy
  - tester-host-has-positive-rokhlin-entropy-action
  - leavitt-unit-group-finitely-presented
---

`L_(F_2)(1,2)^x` is finitely presented, so it embeds in the tester host `U`.

Part (3) of `tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy` shows that POS(`U`) gives RBS(`U`). It also shows that the Bernoulli 2-shift over `U`, restricted to any infinite subgroup, is a free ergodic action of that subgroup with Rokhlin entropy at least `log 2`.

The second prerequisite is open, so this is a valid implication with an open hypothesis.
