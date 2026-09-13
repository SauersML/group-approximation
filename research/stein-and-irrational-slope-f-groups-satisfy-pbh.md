---
rg: 2
id: stein-and-irrational-slope-f-groups-satisfy-pbh
kind: claim
title: The Stein group F_{2,3} and the irrational-slope group F_τ have type (A) actions, so all their subgroups satisfy permutational Boone--Higman
distinct_from:
  stein-group-f23-does-not-embed-in-thompson-v: that shows F_{2,3} does not embed in V; this gives F_{2,3} a type (A) action of its own, so its permutational Boone--Higman property does not come from V.
  stein-group-v23-subgroups-satisfy-pbh: that covers the rearrangement group V_{2,3}, waiting on its finite presentation; this covers the interval groups, whose finite presentation is imported.
  pl-interval-and-circle-groups-have-type-a-orbit-actions: that is the general orbit-action theorem; this is its application to two finitely presented examples.
---

**ESTABLISHED** through `stein-and-irrational-slope-f-groups-pbh-via-orbit-action`
(not independently reviewed; no novelty claimed).

1. The Stein group `F_{2,3}` acts on `Z[1/6] ∩ (0,1)` by an action of type (A). Every
   point stabilizer is isomorphic to `F_{2,3} × F_{2,3}`, and there is one orbit of
   two-element subsets.
2. The irrational-slope group `F_τ`, `τ = (√5 − 1)/2`, acts on `Z[τ] ∩ (0,1)` by an action
   of type (A), with stabilizers `F_τ × F_τ`.

So every subgroup of `F_{2,3}` or of `F_τ` satisfies permutational Boone--Higman, has
solvable word problem, and embeds in a finitely presented simple group.

**Why this is not inherited from V.** `F_{2,3}` does not embed in `V`
(`stein-group-f23-does-not-embed-in-thompson-v`). Its twisted Brin--Thompson envelope
`SV_{F_{2,3}}`, for this action, is a finitely presented simple group containing it.

**For Question 3.4.** These groups are not simple. Their role is that `F_{2,3}` and `F_τ`
are the point stabilizers of the circle groups `T_{2,3}` and `T_τ`. By part 2 of
`pl-interval-and-circle-groups-have-type-a-orbit-actions`, the circle actions are of
type (A) as soon as `T_{2,3}` and `T_τ` are finitely presented.
