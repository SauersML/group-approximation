---
rg: 2
id: function-field-hecke-re-from-sofic-building-action
kind: route
title: A sofic function-field building action makes the Hecke double sofic and the inclusion RE/C
target: function-field-hecke-pair-is-relatively-embeddable
requires:
  - function-field-building-vertex-action-is-sofic
  - sofic-coset-action-makes-amalgam-double-sofic
---

`Lambda=SL_3(F_2[t,1/t])` is a finitely generated linear group over a
field.  By Mal'cev's theorem it is residually finite, hence sofic.  Given a
sofic action `Lambda action Lambda/C` with `C=SL_3(F_2[t])`,
`sofic-coset-action-makes-amalgam-double-sofic` makes `Lambda *_C Lambda`
sofic and `L(C) subset L(Lambda)` `RE/C`.
