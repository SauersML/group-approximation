---
rg: 2
id: gl-n-q-bh-via-rational-leavitt-simple-group
kind: route
title: GL_n(Q) sits in the countable simple group L_Q(1,2)^x / Q^x, so an fp simple overgroup of that group settles every n
target: gl-n-q-embeds-in-fp-simple-group
requires:
  - leavitt-unit-groups-over-every-field-are-simple-mod-scalars
  - rational-leavitt-simple-group-embeds-in-fp-simple-group
---

By `leavitt-unit-groups-over-every-field-are-simple-mod-scalars`, the prefix-code map
```text
g  |->  Σ_(i,j<=n) g_ij s_(a_i) t_(a_j) + s_(1^n) t_(1^n),     a_i = 1^(i-1) 0,
```
embeds `GL_n(Q)` in `L_Q(1,2)^x`, and its image meets the scalars `Q^x` only in `1`.
So `GL_n(Q)` embeds in `Λ = L_Q(1,2)^x / Q^x`. If `Λ` embeds in a finitely presented
simple group `S` (`rational-leavitt-simple-group-embeds-in-fp-simple-group`), then so
does `GL_n(Q)`, for every `n >= 2`.
