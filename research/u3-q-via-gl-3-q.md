---
rg: 2
id: u3-q-via-gl-3-q
kind: route
title: U_3(Q) is a subgroup of GL_3(Q), so the GL_n(Q) root at n = 3 gives it
target: u3-q-embeds-in-fp-simple-group
requires:
  - gl-n-q-embeds-in-fp-simple-group
---

The upper unitriangular matrices form a subgroup `U_3(Q) <= GL_3(Q)`. If
`GL_3(Q)` embeds in a finitely presented simple group `S`, then so does
`U_3(Q)`, by restriction. So `gl-n-q-embeds-in-fp-simple-group` at `n = 3`
implies `u3-q-embeds-in-fp-simple-group`.
