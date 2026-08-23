---
rg: 2
id: lin-canonical-dilation-twirl-proof
kind: route
title: Compute both sides of Lin's explicit column isometry
target: lin-canonical-dilation-twirls-unprotected-left-carriers
requires: []
---

Equation `(LCD2)` follows by applying the adjoint of `(LCD1)` component by
component.  The `g` component of `(p tensor I)V-Vp` is

```text
|G|^(-1/2)(p phi(g^(-1))-phi(g^(-1))p),
```

so summing its squared density seminorm proves `(LCD3)`.  For the Pauli
example, conjugation by `Z` sends `X` to `-X`, and `(LCD4)` follows.

The last scope statement is literal: amplifying a later left operator as
`a tensor I` and compressing through the first isometry gives `(LCD2)`, not
`a`; `A'`-linearity says nothing about this operator because `a` lies in
`A`.  The direct-product and free-product alternatives respectively add
commutation and leave the finite-group hypothesis.
