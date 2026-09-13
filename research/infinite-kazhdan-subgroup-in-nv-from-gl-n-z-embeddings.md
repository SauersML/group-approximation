---
rg: 2
id: infinite-kazhdan-subgroup-in-nv-from-gl-n-z-embeddings
kind: route
title: If GL_3(Z) embeds in some mV, then some nV has an infinite Kazhdan subgroup
target: some-brin-thompson-group-has-an-infinite-kazhdan-subgroup
requires:
  - every-gl-n-z-embeds-in-some-brin-thompson-group
  - elementary-groups-over-fg-rings-have-property-t
---

- By `every-gl-n-z-embeds-in-some-brin-thompson-group`, `GL_3(Z)` embeds in some
  `mV`, and so does its subgroup `SL_3(Z)`.
- `SL_3(Z) = EL_3(Z)`, since `Z` is Euclidean, and it is infinite with property
  (T) (`elementary-groups-over-fg-rings-have-property-t`, `R = Z`, `n = 3`).
- So `mV` contains an infinite Kazhdan subgroup. By Farley's theorem
  (`thompson-v-has-haagerup-property`), `m >= 2`.
