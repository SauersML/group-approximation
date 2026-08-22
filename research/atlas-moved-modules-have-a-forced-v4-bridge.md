---
rg: 2
id: atlas-moved-modules-have-a-forced-v4-bridge
kind: claim
title: The moved Q1920 modules contain a forced commuting holonomy pair joined through the collision V4
artifacts:
  - experiments/atlas_a4_q1920_module_structure.g
  - experiments/atlas_a4_large_k22_intersection_screen.g
  - research/artifacts/atlas-a4-q1920-module-structure.json
  - research/artifacts/atlas-a4-large-k22-intersection-screen.json
---

In any faithful completion, let `a` and `d` be the third labeled
involutions in the radial `A` and `B`, and put

```text
v=a d in V,             v^c=a d^c in V^c.                 (V4-BRIDGE-1)
```

The certified mismatch has order two, so the involutions `a,d` commute.
Conjugating by `c` and using `[a,c]=1` shows that `a,d^c` commute as well.
Inside the marked collision `S4`, the noncentral transpositions `d` and
`d^c` are disjoint and commute.  Therefore

```text
[v,v^c]=1,              v v^c=d d^c in J,                 (V4-BRIDGE-2)
```

and `v,v^c` generate a Klein four group joining `V`, `V^c`, and the normal
collision Klein four.  Moreover the `A`-span of each of `v` and `v^c` has
order eight.  Thus the remaining moved-module problem is not a free amalgam:
it contains a forced pair of three-dimensional `F2[S3]` packets coupled by
`(V4-BRIDGE-2)`.

This does not determine `V cap V^c` or the full group `<V,V^c,A,c>`; those
are the exact remaining rank-two 2-local data.
