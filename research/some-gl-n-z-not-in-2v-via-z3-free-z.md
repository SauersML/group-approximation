---
rg: 2
id: some-gl-n-z-not-in-2v-via-z3-free-z
kind: route
title: If Z^3 * Z does not embed in 2V, then GL_8(Z) does not embed in 2V
target: some-gl-n-z-does-not-embed-in-2v
requires:
  - z3-free-z-does-not-embed-in-2v
  - z3-free-z-embeds-in-gl8z
---

`GL_8(Z)` contains `Z^3 * Z` (`z3-free-z-embeds-in-gl8z`, `k = 3`). A copy of
`GL_8(Z)` inside `2V` would contain `Z^3 * Z`, contradicting
`z3-free-z-does-not-embed-in-2v`. So `n = 8` witnesses the claim.
