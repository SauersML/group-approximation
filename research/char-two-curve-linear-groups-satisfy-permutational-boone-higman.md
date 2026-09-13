---
rg: 2
id: char-two-curve-linear-groups-satisfy-permutational-boone-higman
kind: claim
title: Finitely generated linear groups over characteristic-two fields of transcendence degree at most one, and linear groups over free F_(2^k)-algebras, satisfy permutational Boone--Higman
distinct_from:
  char-two-curve-linear-groups-satisfy-boone-higman: that embeds the same finitely generated groups in the finitely presented simple group L_(F_2)(1,2)^x, which is Boone--Higman; this is the permutational form, which is closed under finite direct products, free products and finite-index overgroups.
  char-two-laurent-linear-groups-satisfy-boone-higman: that is the plain form for the Laurent and free coefficient algebras; this is the permutational form, for those algebras and for curves.
  char-zero-linear-groups-satisfy-permutational-boone-higman: that is the permutational form in characteristic zero; this is the permutational form in characteristic two.
  binary-leavitt-unit-group-satisfies-pbh: that is the permutational property of one group; this is the class of linear inputs that embed in that group.
artifacts:
  - research/artifacts/leavitt-pbh-general-2026-09-13.md
---

**ESTABLISHED (2026-09-13)** through `char-two-linear-pbh-via-binary-leavitt-actor`. Not
independently reviewed. No novelty is claimed: the proof composes established nodes.

## Statement

1. Let `K` be a field of characteristic `2` whose transcendence degree over `F_2` is at
   most `1`, and let `n >= 1`. Every finitely generated subgroup of `GL_n(K)` embeds in a
   finitely presented group admitting an action of type (A).
2. Let `q = 2^k` and `n, m >= 1`. Every subgroup of `GL_n(F_q[t, t^-1])` and of
   `GL_n(F_q<x_1, ..., x_m>)` embeds in a finitely presented group admitting an action of
   type (A).

Examples: every finitely generated subgroup of `SL_n(F_q[t])`, the S-arithmetic groups
`SL_n(O_S)` over global function fields of characteristic two, and the lamplighter
`C_2 wr Z`.

## Why the permutational form matters here

Boone--Higman for these groups was already on main
(`char-two-curve-linear-groups-satisfy-boone-higman`). The permutational class `B_A` is
closed under finite direct products and finite-index overgroups
(`boone-higman-type-a-class-closed-under-finite-extensions`), and under free products
(BFFHZ Corollary F, imported in `aut-free-groups-satisfy-permutational-boone-higman`). So
these inputs can now be combined with the characteristic-zero inputs of
`char-zero-linear-groups-satisfy-permutational-boone-higman`; see
`mixed-characteristic-linear-products-satisfy-pbh`.

The `char-two-laurent-linear-groups-satisfy-boone-higman` node records that the list of
known classes in Belk--Bleak--Matucci--Zaremsky (Theorem 5.1 of *Progress around the
Boone--Higman conjecture*) contains no positive-characteristic linear groups. No further
novelty search was done here.
