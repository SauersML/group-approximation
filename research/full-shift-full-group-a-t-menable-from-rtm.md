---
rg: 2
id: full-shift-full-group-a-t-menable-from-rtm
kind: route
title: "Haagerup for the Turing-machine group RTM(2,1) = M_2 restricts to the full-shift topological full group"
target: full-shift-topological-full-group-is-a-t-menable
requires:
  - turing-machine-group-rtm-2-1-is-a-t-menable
  - nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal
---

This differs from `full-shift-full-group-a-t-menable-from-nv`. That route restricts from all of
`2V`. This one restricts from the intermediate group `M_2 = RTM(2,1)`, so it factors that route
through the Turing-machine prerequisite.

By item 3(c) of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`, `Φ^{-1} [[X]] Φ ≤ M_2`, and
conjugation by `Φ` is an isomorphism of `[[X]]` onto that subgroup. By
`turing-machine-group-rtm-2-1-is-a-t-menable` (in its `M_2` form, which is equivalent by item 1 of
`nv-jacobian-subgroup-contains-turing-machine-distortion`), `M_2` has a proper cnd function.
Restricting it to the subgroup gives a proper cnd function on `[[X]]`.

**Use.** This splits `full-shift-full-group-a-t-menable-from-nv` at the intermediate group:
```text
nV Haagerup  ⟹  RTM(2,1) = M_2 Haagerup  ⟹  [[X]] Haagerup.
```
Both implications are restrictions to subgroups. The middle term contains a distortion element
(`nv-jacobian-subgroup-contains-turing-machine-distortion`). No distortion element of `[[X]]` is
recorded in the graph.
