---
rg: 2
id: thompson-v-hyperlinear-from-leavitt-unit-hyperlinear
kind: route
title: A hyperlinear binary Leavitt unit group makes Thompson's V hyperlinear
target: thompson-v-hyperlinear
requires:
  - binary-leavitt-unit-group-hyperlinear
  - leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear
---

`V` embeds in `L_(F_2)(1,2)^x` (`leavitt-cylinder-swaps-generate-thompson-in-el`),
and hyperlinearity passes to subgroups. So if the unit group is hyperlinear,
`V` is hyperlinear.

This route makes the stakes visible in the graph. Because of the cycle
`leavitt-unit-hyperlinear-from-steinberg-instability` /
`steinberg-instability-from-leavitt-unit-hyperlinear`, any proof of
`binary-leavitt-unit-group-hyperlinear` or of `leavitt-steinberg-hs-unstable`
also answers the open question of whether Thompson's `V` is hyperlinear. The
converse is not known: a hyperlinear `V` does not make the unit group
hyperlinear.
