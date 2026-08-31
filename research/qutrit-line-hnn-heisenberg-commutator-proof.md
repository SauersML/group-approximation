---
rg: 2
id: qutrit-line-hnn-heisenberg-commutator-proof
kind: proof
title: Conjugate the Heisenberg commutator across the line router
target: qutrit-line-hnn-router-cannot-carry-heisenberg-shift
requires:
  - qutrit-line-hnn-router-has-full-source-but-coincident-range
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
---

Conjugate the defining Heisenberg commutator by `U`. Using `(QHC1)`
gives

```text
U^(-1)jU
 =U^(-1)[x,z]U
 =[U^(-1)xU,U^(-1)zU]
 =[U^(-1)xU,j^(-1)].                                   (QHC3)
```

If `U^(-1)xU` commuted with `j`, the right side of `(QHC3)` would be
the identity. But conjugation is injective, so its left side has order three
because `j` has order three. This contradiction proves `(QHC2)`.

The affine qutrit packet has `j=J` as its center, so every one of its
elements commutes with `j`. Hence a relation
`U^(-1)xU=f` with `f` in that packet forces `U^(-1)jU=1` and
therefore `j=1` in the presented group.

Finally, the marked projection is

```text
q=(1+omega^(-1)j+omega^(-2)j^2)/3.
```

If `j=1`, its image in every complex representation is

```text
(1+omega^(-1)+omega^(-2))/3=0.
```

Thus the collapsed relation destroys, rather than routes, the qutrit
corner. This proves the stated obstruction.
