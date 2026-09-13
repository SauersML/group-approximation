---
rg: 2
id: thompson-f-not-automatic-if-amenable-via-rips
kind: route
title: If amenable automatic groups have contractible Rips complexes and F is amenable, then F is not automatic
target: thompson-f-is-not-automatic
requires:
  - amenable-automatic-groups-have-contractible-rips-complexes
  - thompson-f-is-amenable
  - thompson-f-has-no-contractible-rips-complex
---

Suppose `F` is amenable and had an automatic structure. The first prerequisite
would then give a finite generating set `S` and a scale `r` with `P_r(F,S)`
contractible, contradicting `thompson-f-has-no-contractible-rips-complex`. So
`F` is not automatic.

This is the route anticipated in the Attempts of `thompson-f-is-not-automatic`
("the second only together with `thompson-f-is-amenable`").
