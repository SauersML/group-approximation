---
rg: 2
id: full-shift-full-group-a-t-menable-from-nv
kind: route
title: "Haagerup for 2V restricts to the full-shift topological full group"
target: full-shift-topological-full-group-is-a-t-menable
requires:
  - brin-thompson-groups-nv-are-a-t-menable
  - full-shift-topological-full-group-embeds-in-2v
---

By `full-shift-topological-full-group-embeds-in-2v`, `[[X]]` is isomorphic to a subgroup of `2V`.
`brin-thompson-groups-nv-are-a-t-menable`, for `n = 2`, gives a proper cnd function on `2V`.
Restricting a proper cnd function to a subgroup gives a proper cnd function. So `[[X]]` has the
Haagerup property.

**Use (necessity).** The target is a necessary prerequisite of the goal, and it can fail on its own.
If `[[X]]` fails to be Haagerup, then so do `2V` and, through `g ↦ g × id`
(`brin-thompson-nv-embeds-in-mv`), every `nV` with `n ≥ 2`. By
`nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`, item 3(c), the copy of `[[X]]` lies in the
Jacobian subgroup `M_2`, and `M_2 × id ≤ M_n`. So the target tests the fibre half "some cnd function
on `nV` is proper on `M_n`" of item 5 there, and it says nothing about (Q_J).
