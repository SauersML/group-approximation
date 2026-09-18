---
rg: 2
id: gl-n-q-bh-via-permutational-class
kind: route
title: A type (A) actor containing GL_n(Q) embeds in its finitely presented simple twisted Brin--Thompson group
target: gl-n-q-embeds-in-fp-simple-group
requires:
  - gl-n-q-in-permutational-boone-higman-class
  - type-a-action-gives-boone-higman-for-subgroups
---

Fix `n >= 2`. By `gl-n-q-in-permutational-boone-higman-class`, `GL_n(Q)`
embeds in a group `Γ` with an action of type (A) on a set `S`.

Zaremsky's Corollary B (`type-a-action-gives-boone-higman-for-subgroups`,
arXiv:2405.18354) says that any subgroup of a group admitting an action of type
(A) satisfies the Boone--Higman conjecture. Concretely, Theorem A makes the
twisted Brin--Thompson group `SV_Γ` finitely presented. It is simple because
the action is faithful, and `g ↦ τ_g` embeds `Γ` in `SV_Γ`.

The composite `GL_n(Q) -> Γ -> SV_Γ` is the required embedding. The argument
restricts an embedding of `Γ`, so it never uses generators or a word problem of
`GL_n(Q)`. It applies to this countable group unchanged
(`permutational-host-forms-agree-for-countable-inputs`).
