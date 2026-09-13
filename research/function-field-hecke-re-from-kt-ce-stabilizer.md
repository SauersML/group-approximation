---
rg: 2
id: function-field-hecke-re-from-kt-ce-stabilizer
kind: route
title: A Kun--Thom commutation stabilizer at (2,3,3) makes the function-field Hecke pair relatively embeddable
target: function-field-hecke-pair-is-relatively-embeddable
requires:
  - kt-subgroup-is-a-ce-commutation-stabilizer
  - ce-stabilizer-criterion-needs-no-trace
  - kt-double-hyperlinearity-requires-function-field-hecke-re
---

Take a witness for `kt-subgroup-is-a-ce-commutation-stabilizer` at
`(q,r,d)=(2,3,3)`.  The ambient group `G` is residually finite, hence
hyperlinear, so `ce-stabilizer-criterion-needs-no-trace` gives `RE/C` of
`L(Gamma) subset L(G)`.  Item 2 of
`kt-double-hyperlinearity-requires-function-field-hecke-re` transfers `RE/C`
to `L(SL_3(F_2[t])) subset L(SL_3(F_2[t,1/t]))`.
