---
rg: 2
id: stein-group-v23-subgroups-satisfy-pbh
kind: claim
title: Every subgroup of the Stein rearrangement group V_{2,3}, including T_{2,3} and its finitely presented simple subgroups, satisfies permutational Boone--Higman
distinct_from:
  stein-and-irrational-slope-f-groups-satisfy-pbh: that covers the interval groups F_{2,3} and F_τ, whose finite presentation is imported; this covers the rearrangement group V_{2,3} and everything in it, waiting on its finite presentation.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4 in general; this settles it for the finitely presented simple subgroups of V_{2,3} once V_{2,3} is finitely presented.
---

`V_{2,3} = V(Z[1/6], <2,3>)`, the right-continuous piecewise-linear bijections of
`[0,1)` with breakpoints in `Z[1/6]` and slopes in `2^Z 3^Z`, acts on
`Z[1/6] ∩ [0,1)` by an action of type (A). So every subgroup of `V_{2,3}` satisfies
permutational Boone--Higman, has solvable word problem, and embeds in a finitely
presented simple group. That includes the circle group `T_{2,3}` and any finitely
presented simple subgroup.

**Relevance to Question 3.4.** `T_{2,3}` acts on the circle, where BFFHZ point to finitely
presented simple groups that are not MIF (arXiv:2503.21882v2, l.246). This route needs
no MIF.

**Status.** ESTABLISHED (2026-09-18, lane `bh-near-actions`, lane proof, not reviewed) through the route
`stein-group-v23-pbh-via-k-graph-finiteness`: `V_{2,3}` is the full group of a one-vertex 2-graph, hence of
type `F_∞` (`integral-slope-stein-v-groups-are-k-graph-full-groups`), and it is simple. The older route
`stein-group-v23-pbh-via-orbit-action` still waits on `stein-groups-t23-and-v23-are-finitely-presented`, whose
`T_{2,3}` half is open; it is no longer needed.
