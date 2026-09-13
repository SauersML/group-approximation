---
rg: 2
id: opposite-slice-non-re-from-function-field-hecke-non-re
kind: route
title: A non-RE function-field Hecke pair makes the opposite slice non-RE at (2,3,3)
target: opposite-transvection-slice-is-not-relatively-embeddable
requires:
  - function-field-hecke-pair-is-not-relatively-embeddable
  - opposite-slice-contains-function-field-hecke-pair
---

Take `(q,r,d)=(2,3,3)` and `t=x_1`.  Item 4 of
`opposite-slice-contains-function-field-hecke-pair` says that `RE/C` of the
slice implies `RE/C` of `L(SL_3(F_2[t])) subset L(SL_3(F_2[t,1/t]))`.  The
required claim denies the latter.  So the slice inclusion is not `RE/C` at
these parameters, which proves the existential claim.
