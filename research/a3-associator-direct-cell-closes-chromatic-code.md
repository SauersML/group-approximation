---
rg: 2
id: a3-associator-direct-cell-closes-chromatic-code
kind: route
title: Fill each tagged edge by one direct A3 associator cell
target: binary-leavitt-bounded-area-chromatic-code
requires:
  - binary-leavitt-tagged-shift-table-has-centralizer-collisions
---

**INVALIDATED DIRECT-CELL ROUTE.**  For a tagged predecessor column
`C_(ij)=B_i+D_(ij)`, use the two noncommuting positive-root bracketings

```text
[x_12(a),[x_23(1),x_34(C_(ij))]],
[[x_12(a),x_23(1)],x_34(C_(ij))].
```

They are equal by one literal `A_3` associator diagram.  At
`a=A_i+A_j` their common value is the marked long root `x_14(q)`; at
`a=A_j` it is one.  Thus the cell reads the private address payload directly
and contains no distinguished conjugated-mark seams.

`tagged-a3-associator-cell-has-finite-positive-root-model` proves that this
entire direct cell stays inside a finite positive-root fragment.  Its left
regular model makes every associator, tagged multiplication, and range-sum
row exact while the marked long root remains at normalized-HS distance
`sqrt(2)` from one.  Hence the associator is an exact algebraic table but not
a bounded-area MF decoder.

