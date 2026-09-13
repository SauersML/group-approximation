---
rg: 2
id: explicit-eighteen-relator-nonsofic-group-proof
kind: route
title: The eighteen-relator group is the binary Leavitt unit group, which is simple and nonsofic
target: explicit-eighteen-relator-nonsofic-group
requires: [thompson-steinberg-presentation-of-leavitt-unit-group, openai-leavitt-unit-nonsofic, binary-leavitt-unit-group-is-simple]
artifacts:
  - research/artifacts/thompson-steinberg-presentation-2026-09-12.md
---

By `thompson-steinberg-presentation-of-leavitt-unit-group` the presented group is isomorphic to
`L_(F_2)(1,2)^x`. That group is not sofic (`openai-leavitt-unit-nonsofic`; independently
kernel-checked as `universalLeavittUnits_not_isSofic`) and is simple
(`binary-leavitt-unit-group-is-simple`). The presentation is finite by construction. QED.
