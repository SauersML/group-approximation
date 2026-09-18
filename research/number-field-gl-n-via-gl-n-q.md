---
rg: 2
id: number-field-gl-n-via-gl-n-q
kind: route
title: Restrict scalars from K to Q and use a finitely presented simple host of GL_nd(Q)
target: number-field-gl-n-embeds-in-fp-simple-group
requires:
  - gl-n-q-embeds-in-fp-simple-group
  - number-field-linear-groups-embed-in-gl-n-q
---

Let `K` have degree `d`. `GL_n(K) <= GL_(nd)(Q)` by
`number-field-linear-groups-embed-in-gl-n-q`, and `GL_(nd)(Q)` embeds in a
finitely presented simple group by `gl-n-q-embeds-in-fp-simple-group`.
Embeddability in a finitely presented simple group passes to subgroups.
