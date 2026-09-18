---
rg: 2
id: free-centre-by-metabelian-rank-two-pbh-via-linearity
kind: route
title: Linearity of F_2/[F_2'',F_2] over Q(x,y) puts it in the permutational Boone--Higman class
target: free-centre-by-metabelian-group-of-rank-two-satisfies-pbh
requires:
  - free-centre-by-metabelian-group-of-rank-two-is-linear
  - char-zero-linear-groups-satisfy-permutational-boone-higman
---

By `free-centre-by-metabelian-group-of-rank-two-is-linear`, `C_2` is a finitely generated
subgroup of `GL_4(Q(x, y))`, and `Q(x, y)` has characteristic zero. By
`char-zero-linear-groups-satisfy-permutational-boone-higman`, `C_2` lies in `B_A`.
Membership in `B_A` passes to subgroups, and every group in `B_A` embeds in a finitely
presented simple group. ∎
