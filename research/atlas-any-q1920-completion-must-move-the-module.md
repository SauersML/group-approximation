---
rg: 2
id: atlas-any-q1920-completion-must-move-the-module
kind: claim
title: Every faithful completion of either marked Q1920 seam must move its characteristic C2^5 module
artifacts:
  - experiments/atlas_a4_q1920_module_structure.g
  - research/artifacts/atlas-a4-q1920-module-structure.json
distinct_from:
  atlas-q1920-agl5-has-no-collision-involution: that assumes the module is normal and self-centralizing so the whole completion embeds in Hol(V); this removes the self-centralizing hypothesis by using only the conjugation action on V.
  atlas-q1920-holomorph-has-no-collision-involution: that assumes the whole local Q is normalized; this proves that even its characteristic module cannot remain normal.
---

Let `L` be a group containing either marked local `Q=Q1920`, the first
packet `F`, and the collision `J=S4` faithfully.  Write `V ~= C2^5` for the
unique order-32 normal subgroup of `Q`, `A=<r,u>`, and `B=<y,b>`.

Suppose for contradiction that `V normal L`.  Conjugation by the collision
involution `c` induces a linear automorphism of `V`.  Because `c` centralizes
`A`, this automorphism lies in

```text
C_GL(V)(A),        |C_GL(V)(A)|=6.                         (Q1920-LIN-1)
```

The collision relations descend under every conjugation representation.
Exact evaluation on the three involutions in `(Q1920-LIN-1)` shows that none
satisfies both

```text
(c t)^3=1,          t c s c t^-1 c s t c=1.               (Q1920-LIN-2)
```

Therefore `c` acts trivially on `V`.

Now use the radial lift mismatch.  The third labeled involutions `a in A`
and `d in B` have the same image in `Q/V`, and

```text
v = a d^-1 in V.                                          (Q1920-LIN-3)
```

The element `c` centralizes `a` by the first-packet relations and centralizes
`v` by the preceding paragraph, so `(Q1920-LIN-3)` forces it to centralize
`d`.  But in the faithful marked collision `S4`, that third labeled
`B`-involution is not the unique `B`-involution centralized by `c`.  This is
a contradiction.  Hence `V` is not normal in `L`.

The argument allows an arbitrarily large `C_L(V)` and does not assume that
`L` is finite.  Thus every faithful completion must contain a genuinely
distinct conjugate `V^c`.
