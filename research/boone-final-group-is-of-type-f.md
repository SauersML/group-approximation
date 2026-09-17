---
rg: 2
id: boone-final-group-is-of-type-f
kind: claim
title: The final Aanderaa--Cohen--Boone group of every modular machine is of type F
distinct_from:
  boone-final-group-finitely-presented: That is finite presentability (type F_2) of the same group G_M; this gives a finite K(G_M,1), hence type F_n for every n, and needs the freeness of the final associated subgroup, which finite presentability does not.
  some-type-f-group-has-unsolvable-word-problem: That imports from Collins--Miller a group with a finite ASPHERICAL PRESENTATION; this proves type F (a finite 3-dimensional K(G,1)) for the specific machine-checked group G_M, with no literature input about asphericity of Boone groups.
---

For every modular machine `M`, the group `G_M` of the Novikov--Boone chain
(`FinalGroup M`: the tower `G'_M` of [[boone-hnn-tower-embeds-base-group]] with
the stable letter `k` adjoined over `<t>' = <t, r_1, ..., r_n>` with the identity
identification) has a finite `K(G_M, 1)`, of dimension at most 3. In particular
`G_M` is of type `F`, and of type `F_n` for every `n`; its geometric and
cohomological dimensions are at most 3.

The structure: `G = <t, x, y | xy = yx> = Z * Z^2` has the finite 2-dimensional
`K(G,1)` `S^1 v T^2`; `G'_M` is a multiple HNN extension of `G` along subgroups
isomorphic to `G`; and `G_M` is an HNN extension of `G'_M` along the free group
of rank `n + 1` of [[boone-halting-lift-is-free-on-t-and-stable-letters]]. The
graph-of-spaces construction with finite edge spaces is aspherical.

Proof: route `boone-final-group-is-of-type-f-proof`.
