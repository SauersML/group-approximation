---
rg: 2
id: kourovka-7-19-via-hard-type-a-actor
kind: route
title: Take the twisted Brin-Thompson group of an explicit type (A) actor whose orbit problem is not primitive recursive
target: kourovka-7-19-explicit-fp-simple-group-with-non-pr-word-problem
requires: [explicit-type-a-actor-with-non-pr-orbit-problem, twisted-brin-thompson-finite-presentation-criterion, twisted-brin-thompson-wp-equals-actor-orbit-problem]
---

Let `G` act faithfully on `S` with type (A), explicitly, with `OP(G,S)` not primitive recursive
(`explicit-type-a-actor-with-non-pr-orbit-problem`).

1. By `twisted-brin-thompson-finite-presentation-criterion`, `SV_G` is finitely presented and simple. It is explicitly
   described by its brick generators from `G` and the action (Belk--Zaremsky); a finite presentation is
   supplied by Zaremsky's proof, which we did not check for effectiveness.
2. By (a) of `twisted-brin-thompson-wp-equals-actor-orbit-problem`, `OP(G,S)` reduces to the word problem of
   `SV_G` by linear-time substitutions.
3. Primitive recursive functions are closed under composition with linear-time maps. So if the word problem of
   `SV_G` were primitive recursive, so would `OP(G,S)` be, contrary to hypothesis. `∎`
