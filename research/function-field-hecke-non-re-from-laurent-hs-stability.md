---
rg: 2
id: function-field-hecke-non-re-from-laurent-hs-stability
kind: route
title: Flexible HS stability of SL_3(F_2[t,1/t]) makes the function-field Hecke pair non-RE
target: function-field-hecke-pair-is-not-relatively-embeddable
requires:
  - sl3-laurent-f2-is-flexibly-hs-stable
  - function-field-hecke-pair-is-perfect-codense-kazhdan
---

Apply item 4 of `function-field-hecke-pair-is-perfect-codense-kazhdan` in
case (i) with `(q,r)=(2,3)`.  If `SL_3(F_2[t,1/t])` is flexibly HS stable, the
centralizer HNN group over `SL_3(F_2[t])` is non-hyperlinear.  Hence
`L(SL_3(F_2[t])) subset L(SL_3(F_2[t,1/t]))` is not `RE/C`.
