---
rg: 2
id: leavitt-square-units-pbh-via-chen-line-action
kind: route
title: The tensor-square line action is 2-transitive with finitely generated stabilizers, so it is of type (A)
target: leavitt-square-unit-groups-mod-scalars-satisfy-pbh
requires:
  - leavitt-square-units-act-two-transitively-on-chen-lines
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - two-transitive-action-reduces-type-a-to-two-clauses
---

By `leavitt-square-units-act-two-transitively-on-chen-lines`:
- `G^(2)_p` acts faithfully and 2-transitively on the lines of `F_p[D × D]`, a set with
  more than two elements;
- the stabilizer of one line is isomorphic to the finitely generated group `H`.

`G^(2)_p` is finitely presented by `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`.

By `two-transitive-action-reduces-type-a-to-two-clauses`, a faithful 2-transitive action of
a finitely presented group with one finitely generated point stabilizer is of type (A).
So `G^(2)_p` admits an action of type (A), and every subgroup of `G^(2)_p` embeds in
`G^(2)_p`. That is the defining condition of permutational Boone--Higman, in the form of
BFFHZ Theorem C (i). `∎`
