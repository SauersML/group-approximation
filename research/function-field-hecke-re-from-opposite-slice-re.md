---
rg: 2
id: function-field-hecke-re-from-opposite-slice-re
kind: route
title: RE/C of the opposite slice at (2,3,3) gives RE/C of the function-field Hecke pair
target: function-field-hecke-pair-is-relatively-embeddable
requires:
  - opposite-transvection-slice-is-relatively-embeddable
  - opposite-slice-contains-function-field-hecke-pair
---

Specialize the required `RE/C` claim to `(q,r,d)=(2,3,3)`.  The third bullet
of item 4 of `opposite-slice-contains-function-field-hecke-pair` transfers
`RE/C` from `L(Gamma) subset L(P)` to
`L(SL_3(F_2[t])) subset L(SL_3(F_2[t,1/t]))`.
