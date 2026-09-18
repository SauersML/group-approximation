---
rg: 2
id: gl-n-q-bh-via-leavitt-resolvent-units
kind: route
title: Embed GL_n(Q) in the derived unit group of the Leavitt resolvent ring modulo its centre
target: gl-n-q-embeds-in-fp-simple-group
requires:
  - leavitt-resolvent-ring-is-fp-simple-of-char-zero
  - leavitt-resolvent-derived-units-mod-centre-fp-simple
---

Deduction. Let `n >= 2`.

By `leavitt-resolvent-ring-is-fp-simple-of-char-zero`, part 3:
- the map `g ↦ diag(g, det(g)^(-1), 1)`, followed by `M_(n+2)(Q) ⊆ M_(n+2)(R_L) ≅ R_L`,
  embeds `GL_n(Q)` in `D = [R_L^x, R_L^x]`;
- the image meets `Z(D)` trivially: a central element commutes with the image of
  `SL_(n+2)(Q) <= D`, so it is scalar in `M_(n+2)(Q)`, and `diag(g, det(g)^(-1), 1)` is
  scalar only for `g = 1`.

Hence `GL_n(Q)` embeds in `D/Z(D)`. That group is finitely presented and simple by
`leavitt-resolvent-derived-units-mod-centre-fp-simple`.
