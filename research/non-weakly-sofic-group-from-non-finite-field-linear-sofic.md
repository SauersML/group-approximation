---
rg: 2
id: non-weakly-sofic-group-from-non-finite-field-linear-sofic
kind: route
title: A group that is not linear sofic over finite fields gives a two-generator simple group that is not weakly sofic
target: non-weakly-sofic-group-exists
requires: [non-finite-field-linear-sofic-group-exists, non-weakly-sofic-iff-non-finite-field-linear-sofic-group]
---

Let `Gamma` witness `non-finite-field-linear-sofic-group-exists`. By item (2) => (4) of
`non-weakly-sofic-iff-non-finite-field-linear-sofic-group`, some two-generator simple group containing a finitely
generated subgroup of `Gamma` is not weakly sofic. That group witnesses this root.

The route does not fire until its first prerequisite is established, which is open. The converse direction is recorded
on the equivalence claim: a witness of this root is not linear sofic over finite fields. So no weaker target for this
root exists on the rank side.
