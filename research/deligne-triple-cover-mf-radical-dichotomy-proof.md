---
rg: 2
id: deligne-triple-cover-mf-radical-dichotomy-proof
kind: route
title: Bound the MF radical by the finite residual and use the universal MF quotient
target: deligne-triple-cover-mf-radical-dichotomy
requires:
  - deligne-triple-cover-finite-residual-is-center
---

Every finite-dimensional representation is a norm-matrix-corona
representation, so

```text
Rad_MF(E_3)<=Res_fin(E_3)=C_3.
```

Since `C_3` has prime order, its only subgroups are `1` and `C_3`, proving
`(DMD1)`.  The first two assertions in `(DMD2)` are therefore equivalent.
Finally a group is MF exactly when its universal homomorphism to the product
of all norm-matrix coronas is injective, equivalently when its MF radical is
trivial.  This gives the last equivalence.

