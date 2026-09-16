---
rg: 2
id: amenable-automatic-ea-via-f-infinity-amenable-ea
kind: route
title: If every amenable F_infinity group is elementary amenable, so is every amenable automatic group
target: amenable-automatic-groups-are-elementary-amenable
requires:
  - every-f-infinity-amenable-group-is-elementary-amenable
  - automatic-groups-are-of-type-f-infinity
---

## Why sufficient

Let `G` be amenable and automatic. By `automatic-groups-are-of-type-f-infinity`, `G` is of
type `F_∞`. So `G` is an amenable group of type `F_∞`, and
`every-f-infinity-amenable-group-is-elementary-amenable` makes it elementary amenable.

This is Proposition 7 in
`research/artifacts/amenable-automatic-groups-are-virtually-abelian-2026-09-16.md`,
Section 6. It places the target under the nonexistence answer to Zaremsky Problem 1.12.
