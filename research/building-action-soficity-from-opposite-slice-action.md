---
rg: 2
id: building-action-soficity-from-opposite-slice-action
kind: route
title: A sofic opposite-slice action restricts to a sofic function-field building action
target: function-field-building-vertex-action-is-sofic
requires:
  - opposite-transvection-coset-action-is-sofic
  - opposite-slice-contains-function-field-hecke-pair
---

Specialize the required soficity claim to `(q,r,d)=(2,3,3)`.  The first
bullet of item 4 of `opposite-slice-contains-function-field-hecke-pair`
restricts the action to `Lambda_1` and to the orbit of the base site.  That
orbit is `SL_3(F_2[t,1/t]) action SL_3(F_2[t,1/t])/SL_3(F_2[t])`, which is the
type-zero vertex action by (HP2).
