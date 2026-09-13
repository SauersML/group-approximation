---
rg: 2
id: opposite-slice-re-from-sofic-coset-action
kind: route
title: A sofic opposite-slice coset action makes the slice double sofic and the inclusion RE/C
target: opposite-transvection-slice-is-relatively-embeddable
requires:
  - opposite-transvection-coset-action-is-sofic
  - sofic-coset-action-makes-amalgam-double-sofic
  - kun-thom-nonsofic-wreath
---

Theorem E in `kun-thom-nonsofic-wreath` makes the ambient Kun--Thom group
residually finite.  Its subgroup `P` is therefore residually finite, hence
sofic.  Given a sofic action `P action P/Gamma`,
`sofic-coset-action-makes-amalgam-double-sofic` makes `P *_Gamma P` sofic and
`L(Gamma) subset L(P)` `RE/C`.  This holds for each `(q,r,d)`.
