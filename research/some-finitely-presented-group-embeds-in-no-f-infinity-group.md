---
rg: 2
id: some-finitely-presented-group-embeds-in-no-f-infinity-group
kind: claim
title: "Some finitely presented group embeds in no group of type F_infinity"
distinct_from:
  some-type-fn-group-embeds-in-no-type-fn-plus-1-group: that asks for a group of type F_n with no F_{n+1} host, which implies this claim; this only forbids F_infinity hosts
  every-finitely-presented-group-embeds-in-an-f-infinity-group: that is the negation of this claim
---

There is a finitely presented group that embeds in no group of type `F_∞`.
This is the negative answer to the second part of Zaremsky Problem 1.1 (root
`zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1`).

If any witness exists, a universal finitely presented group `U` (Higman 1961)
is a witness, because `U` contains every finitely presented group. This claim
is compatible with an affirmative first part only if `U` has hosts
`K_3 <= K_4 <= ...` with `K_m` of type `F_m` but none of type `F_∞`.

It follows from `some-type-fn-group-embeds-in-no-type-fn-plus-1-group`
through the route `no-f-infinity-host-from-no-type-fn-plus-1-host`.

## Attempts

- Deferred to lane z1-01-embed-neg. The dead obstruction strategies recorded
  on `some-type-fn-group-embeds-in-no-type-fn-plus-1-group` (cardinality, word
  problem complexity) apply here unchanged.
