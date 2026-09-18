---
rg: 2
id: free-centre-by-metabelian-group-of-rank-two-satisfies-pbh
kind: claim
title: The free centre-by-metabelian group F_2/[F_2'',F_2] lies in the permutational Boone--Higman class, so it embeds in a finitely presented simple group
distinct_from:
  free-centre-by-metabelian-groups-satisfy-boone-higman: that is the same statement for every rank r >= 2 and stays OPEN for r >= 3; this is the rank-2 case.
  free-centre-by-metabelian-group-of-rank-two-is-linear: that is the faithful 4x4 representation; this is its Boone--Higman consequence through the characteristic-zero linear node.
---

**ESTABLISHED** by `free-centre-by-metabelian-rank-two-pbh-via-linearity` (lane proof,
not independently reviewed; no novelty claimed).

`C_2 = F_2/[F_2'', F_2]` lies in `B_A`. So `C_2` and all its subgroups embed in a
finitely presented simple group; by BFFHZ Theorem C that group can be taken to be a
twisted Brin--Thompson group.

**Trust surface.** The linearity step is the lane proof
`free-centre-by-metabelian-rank-two-linearity-proof`, which is elementary. The Boone--Higman
step is the characteristic-zero linear node of main, which has internal reviews only. The
published literature reaches only f.g. subgroups of `GL_n(Q)` (Zaremsky), and `C_2` is
not of that form: its centre `F''/[F'',F]` is free abelian of infinite rank, and f.g.
solvable subgroups of `GL_n(Q)` have finite Prüfer rank.
