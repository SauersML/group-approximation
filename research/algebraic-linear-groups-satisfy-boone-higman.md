---
rg: 2
id: algebraic-linear-groups-satisfy-boone-higman
kind: claim
title: Every finitely generated linear group over a number field embeds in a finitely presented simple group
distinct_from:
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's rational statement; this extends it to every field algebraic over Q, by restriction of scalars.
  char-zero-linear-groups-satisfy-boone-higman: that is the open characteristic-zero class of every transcendence degree; this is its established transcendence-degree-zero part.
---

**ESTABLISHED.** Let `K` be a field algebraic over `Q`, and let
`H <= GL_n(K)` be finitely generated. Then `H` embeds in a finitely presented
simple group.

Equivalently, every finitely generated subgroup of `GL_n(Qbar)` satisfies the
Boone--Higman conjecture.

This follows routinely from `rational-linear-groups-satisfy-boone-higman`, and no
novelty is claimed; the reduction may be implicit in Zaremsky's paper. It is
recorded because it is the transcendence-degree-zero part of
`char-zero-linear-groups-satisfy-boone-higman`.

Positive transcendence degree is partly established by
`polynomial-linear-groups-satisfy-boone-higman` (2026-09-12). It covers
subgroups of `GL_N(Z[1/m][t_1..t_k])`, including `SL_3(Z[t])`. The first open
cases are `SL_3(Z[t^(+-1)])` and the finitely generated subgroups of
`GL_n(Q(t))` whose entries need non-constant denominators.
