---
rg: 2
id: f-infinity-fcd-contractible-rips-from-1-21-and-4-07
kind: route
title: Yes to Problems 1.21 and 4.7 together give yes to Problem 4.6
target: f-infinity-finite-cd-groups-have-contractible-rips
requires:
  - f-infinity-groups-of-finite-cd-are-of-type-f
  - every-type-f-group-has-a-contractible-rips-complex
---

Let `G` be of type `F_∞` with `cd G < ∞`. By
`f-infinity-groups-of-finite-cd-are-of-type-f`, `G` is of type F. By
`every-type-f-group-has-a-contractible-rips-complex`, some Rips complex of `G`
(some finite generating set, some scale) is contractible. That is the target, and
both claims use the same weak reading (some generating set, some scale).

Together with `f-infinity-fcd-type-f-from-contractible-rips` and
`type-f-contractible-rips-from-f-infinity-fcd-rips` this records an equivalence:
the target holds iff both required claims hold. The dependency cycle this creates
is intended. A least fixpoint never fires a cycle, so none of the three claims
establishes itself.
