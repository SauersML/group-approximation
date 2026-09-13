---
rg: 2
id: leavitt-units-pbh-via-chen-module-line-action
kind: route
title: The line action on the Chen module is 2-transitive with finitely generated stabilizers, so it is of type (A)
target: leavitt-unit-groups-mod-scalars-satisfy-pbh
requires:
  - leavitt-units-act-two-transitively-on-chen-module-lines
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - two-transitive-action-reduces-type-a-to-two-clauses
---

By `leavitt-units-act-two-transitively-on-chen-module-lines`:
- `G_p` acts faithfully and 2-transitively on the set of lines of `F_p[D]`;
- that set has more than two elements;
- the stabilizer of one line is finitely generated.

`G_p` is finitely presented by `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`.

By `two-transitive-action-reduces-type-a-to-two-clauses`, a faithful 2-transitive action
of a finitely presented group with one finitely generated point stabilizer is of type
(A). So `G_p` admits an action of type (A).

Every subgroup of `G_p` embeds in `G_p`. That is the defining condition of permutational
Boone--Higman, in the form of BFFHZ Theorem C (i). `∎`
