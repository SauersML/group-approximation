---
rg: 2
id: thompson-f-not-amenable-if-automatic-via-rips
kind: route
title: If amenable automatic groups have contractible Rips complexes and F is automatic, then F is not amenable
target: thompson-f-is-not-amenable
requires:
  - amenable-automatic-groups-have-contractible-rips-complexes
  - thompson-f-is-automatic
  - thompson-f-has-no-contractible-rips-complex
---

Suppose `F` is automatic and were amenable. The first prerequisite would then
give a finite generating set `S` and a scale `r` with `P_r(F,S)` contractible,
contradicting `thompson-f-has-no-contractible-rips-complex`. So `F` is not
amenable.
