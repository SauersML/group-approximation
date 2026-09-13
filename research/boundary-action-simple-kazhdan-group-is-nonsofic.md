---
rg: 2
id: boundary-action-simple-kazhdan-group-is-nonsofic
kind: claim
title: Over a finite field the boundary mirror of the Pestov group, EL_N(LC(∂F_d,k) ⋊ F_d) mod centre, is nonsofic
distinct_from:
  boundary-action-elementary-simple-kazhdan-not-mf: that shows the same group has no nontrivial MF quotient; this shows it is not even sofic, via a unital Leavitt family and the Lean nonsoficity theorem.
  purely-infinite-simple-algebras-have-nonsofic-el-groups: that covers unit, GL and EL groups of purely infinite simple algebras; this covers the projective quotients EL_N/C for central scalar C, for the explicit boundary ring, with no Ara–Goodearl–Pardo input.
---

Let `k` be a finite field, `d >= 2`, `R_∂ = LC(∂F_d, k) ⋊ F_d` and `N >= 2`. For every subgroup
`C ≤ EL_N(R_∂) ∩ k^x I_N`, the group `EL_N(R_∂)/C` contains an isomorphic copy of `EL_N(R_∂)` and is nonsofic.

In particular, for `N >= 3`, `S_∂ = EL_N(R_∂)/Z(EL_N(R_∂))` is nonsofic. With
`boundary-action-elementary-simple-kazhdan-not-mf`, `S_∂` is an infinite, finitely generated, simple Kazhdan group
that is nonsofic and has no nontrivial MF quotient.

The mirror is sharp. The Pestov group `EL_3(LC(X,F_q) ⋊ Z)/Z` is LEF, hence sofic. The same construction over the
paradoxical boundary action lands on the other side of both lines.

ESTABLISHED by `boundary-action-simple-kazhdan-group-is-nonsofic-proof` (unreviewed).
