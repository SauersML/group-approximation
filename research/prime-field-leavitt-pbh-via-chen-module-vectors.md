---
rg: 2
id: prime-field-leavitt-pbh-via-chen-module-vectors
kind: route
title: The unit group of the F_p Leavitt algebra carries a type (A) action on the nonzero vectors of its Chen module
target: prime-field-leavitt-unit-groups-satisfy-pbh
requires:
  - prime-field-leavitt-units-act-with-type-a-on-chen-vectors
---

By `prime-field-leavitt-units-act-with-type-a-on-chen-vectors`, `L_(F_p)(1,2)^×` acts with
type (A) on `F_p[D] ∖ {0}`, for every prime `p`.

The group is therefore itself a finitely presented group admitting an action of type (A),
and it embeds in that group through the identity. This is the target statement.

Unlike `prime-field-leavitt-pbh-via-covered-module-amalgam`, this route needs no finite
presentation of a module extension and no covered generating set. `∎`
