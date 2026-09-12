---
rg: 2
id: non-rf-hyperbolic-from-non-vtf-hyperbolic
kind: route
title: A hyperbolic group with invisible torsion is not residually finite
target: non-residually-finite-hyperbolic-group
requires:
  - non-virtually-torsion-free-hyperbolic-group
  - hyperbolic-rf-question-equals-vtf-question
---

Direction (2) => (1) of `hyperbolic-rf-question-equals-vtf-question`.  A
word-hyperbolic group that is not virtually torsion-free has a nonidentity
element of finite order in its finite residual, by the finite torsion-carrier
criterion, so it is not residually finite.

This half is one line; its partner `non-vtf-hyperbolic-via-residual-cyclic-filling`
is the half that needs a Dehn filling.  The two routes form an intended
equivalence cycle (see the partner route); do not delete either to silence the
cycle warning.
