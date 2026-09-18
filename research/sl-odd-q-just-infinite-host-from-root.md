---
rg: 2
id: sl-odd-q-just-infinite-host-from-root
kind: route
title: A finitely presented simple overgroup of GL_m(Q) is a just-infinite host for SL_m(Q)
target: sl-odd-q-has-fp-just-infinite-host
requires: [gl-n-q-embeds-in-fp-simple-group]
---

Assume the root. For each odd `m >= 3`, `GL_m(Q)` embeds in a finitely presented
simple group `T_m`, and restricting gives an embedding `ρ_m` of
`SL_m(Q) <= GL_m(Q)` in `T_m`. `T_m` is infinite and simple, so its only
nontrivial normal subgroup is `T_m` itself, of index 1. So `(T_m, ρ_m)` witnesses
`sl-odd-q-has-fp-just-infinite-host` for every odd `m`. ∎

This route records that the relaxed target is equivalent to the root, not weaker
than it.
