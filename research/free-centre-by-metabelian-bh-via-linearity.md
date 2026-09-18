---
rg: 2
id: free-centre-by-metabelian-bh-via-linearity
kind: route
title: Every F_n/[F_n'',F_n] is linear in characteristic zero, so it lies in the permutational Boone--Higman class
target: free-centre-by-metabelian-groups-satisfy-boone-higman
requires:
  - free-centre-by-metabelian-groups-are-linear
  - char-zero-linear-groups-satisfy-permutational-boone-higman
---

By `free-centre-by-metabelian-groups-are-linear`, `C_r` is a finitely generated subgroup
of `GL_N(Q(x_1, …, x_r))`, which has characteristic zero. By
`char-zero-linear-groups-satisfy-permutational-boone-higman`, `C_r` is in `B_A`. So it
embeds in a finitely presented simple group; by BFFHZ Theorem C, a twisted Brin–Thompson
group. This holds for every finite `r >= 2`. ∎
