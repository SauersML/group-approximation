---
rg: 2
id: turing-machine-group-rtm-2-1-a-t-menable-from-nv
kind: route
title: "Haagerup for 2V restricts to the Jacobian subgroup M_2, which is RTM(2,1)"
target: turing-machine-group-rtm-2-1-is-a-t-menable
requires:
  - brin-thompson-groups-nv-are-a-t-menable
  - nv-jacobian-subgroup-contains-turing-machine-distortion
---

`brin-thompson-groups-nv-are-a-t-menable`, for `n = 2`, gives a cnd function on `2V` that is
proper. Its restriction to the subgroup `M_2` is cnd and proper. By item 1 of
`nv-jacobian-subgroup-contains-turing-machine-distortion`, `M_2 ≅ RTM(2,1)`, so `RTM(2,1)` has the
Haagerup property.

**Use (necessity).** The target is a necessary prerequisite of the goal, and it can fail on its own.
If `RTM(2,1)` is not Haagerup, then neither is `2V`. Through `g ↦ g × id`
(`brin-thompson-nv-embeds-in-mv`), neither is any `nV` with `n ≥ 2`. It is the "proper on `M_2`"
face of the fibre half in item 5 of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`, and it
says nothing about (Q_J). It contains the `[[X]]` prerequisite
(`full-shift-full-group-a-t-menable-from-nv`) and, unlike that one, it contains a distortion
element.
