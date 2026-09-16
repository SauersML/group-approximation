---
rg: 2
id: amenable-automatic-groups-are-elementary-amenable
kind: claim
title: Every amenable automatic group is elementary amenable
distinct_from:
  amenable-automatic-groups-are-virtually-abelian: that concludes virtually abelian; this concludes only elementary amenable, which is weaker, and is the half of that claim not covered by Thurston's conjecture
  every-f-infinity-amenable-group-is-elementary-amenable: that is the same conclusion for every amenable group of type F_infinity; this is its restriction to automatic groups, which are of type F_infinity
---

**OPEN.** If `G` is automatic and amenable, then `G` lies in Chou's class `EG` of
elementary amenable groups.

It matters here because, together with `soluble-automatic-groups-are-virtually-abelian`,
it gives `amenable-automatic-groups-are-virtually-abelian` (route
`amenable-automatic-va-via-ea-and-soluble-case`). It follows from that claim (route
`amenable-automatic-ea-from-virtually-abelian-case`) and from
`every-f-infinity-amenable-group-is-elementary-amenable` (route
`amenable-automatic-ea-via-f-infinity-amenable-ea`).

## Attempts

- 2026-09-16 (lane swarm-amenable-automatic-groups-are-): **no mechanism.** Automaticity
  adds a regular normal form, the fellow traveller property, type `F_∞` and a quadratic
  Dehn function. None of these gives a finite subnormal series with elementary amenable
  factors. The general `F_∞` problem is open for the same reason (see the Attempts of
  `every-f-infinity-amenable-group-is-elementary-amenable`).
- **Growth gives no constraint.** By
  `automatic-groups-virtually-abelian-or-free-subsemigroup`, a counterexample has a free
  subsemigroup of rank 2, and so exponential growth. Such groups are not automatically
  excluded from `EG`. From memory and unverified: every finitely generated elementary
  amenable group that is not virtually nilpotent has a free subsemigroup (Chou 1980).
  The free subsemigroup therefore does not separate the two classes.
- **The test case is Thompson's group `F`.** `F` is of type `F_∞` and not elementary
  amenable. So if `F` were amenable and automatic, this claim would fail. Conversely,
  this claim implies `thompson-f-is-not-both-amenable-and-automatic`. That route is not
  recorded, because "`F` is not elementary amenable" has no node with a verified
  citation yet.
